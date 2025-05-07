// Lean compiler output
// Module: Lean.Compiler.IR.Borrow
// Imports: Lean.Compiler.ExportAttr Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds
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
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(size_t, size_t, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_OwnedSet_getHash(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_whileModifing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_ParamMap_getHash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToFormatParamMap;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_getHash___boxed(lean_object*);
lean_object* l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_getHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instHashableKey;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instBEqKey;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instHashableKey;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap;
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instBEqKey;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_contains___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn(lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_OwnedSet_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_OwnedSet_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_OwnedSet_getHash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_getHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_OwnedSet_getHash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_OwnedSet_getHash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_IR_Borrow_OwnedSet_beq(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_IR_Borrow_OwnedSet_getHash(x_4);
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
x_29 = l_Lean_IR_Borrow_OwnedSet_getHash(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_IR_Borrow_OwnedSet_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_1, x_2, x_7);
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
x_13 = l_Lean_IR_Borrow_OwnedSet_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(0);
x_7 = lean_array_get_size(x_5);
x_8 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_array_uset(x_5, x_22, x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_shiftl(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_box(0);
x_36 = lean_array_uset(x_5, x_22, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_6, x_23);
x_38 = lean_array_uset(x_36, x_22, x_37);
lean_ctor_set(x_1, 1, x_38);
return x_1;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; lean_object* x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_array_get_size(x_40);
x_43 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_44 = lean_unsigned_to_nat(32u);
x_45 = lean_uint64_of_nat(x_44);
x_46 = lean_uint64_shift_right(x_43, x_45);
x_47 = lean_uint64_xor(x_43, x_46);
x_48 = lean_unsigned_to_nat(16u);
x_49 = lean_uint64_of_nat(x_48);
x_50 = lean_uint64_shift_right(x_47, x_49);
x_51 = lean_uint64_xor(x_47, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_usize_of_nat(x_54);
x_56 = lean_usize_sub(x_53, x_55);
x_57 = lean_usize_land(x_52, x_56);
x_58 = lean_array_uget(x_40, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_nat_add(x_39, x_54);
lean_dec(x_39);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_58);
x_62 = lean_array_uset(x_40, x_57, x_61);
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
lean_object* x_69; lean_object* x_70; 
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_box(0);
x_73 = lean_array_uset(x_40, x_57, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_41, x_58);
x_75 = lean_array_uset(x_73, x_57, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_39);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_6 = lean_unsigned_to_nat(32u);
x_7 = lean_uint64_of_nat(x_6);
x_8 = lean_uint64_shift_right(x_5, x_7);
x_9 = lean_uint64_xor(x_5, x_8);
x_10 = lean_unsigned_to_nat(16u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_sub(x_15, x_17);
x_19 = lean_usize_land(x_14, x_18);
x_20 = lean_array_uget(x_3, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_OwnedSet_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_name_eq(x_10, x_12);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_ParamMap_getHash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Name_hash___override(x_4);
x_7 = lean_uint64_of_nat(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_getHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instHashableKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_getHash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed), 1, 0);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Name_toString(x_18, x_21, x_19);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_22);
x_6 = x_3;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed), 1, 0);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_Name_toString(x_23, x_26, x_24);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_6 = x_28;
goto block_16;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed), 1, 0);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Name_toString(x_30, x_34, x_32);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_mk_string_unchecked(":", 1, 1);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_36);
x_39 = lean_mk_string_unchecked("block_", 6, 6);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
x_6 = x_43;
goto block_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed), 1, 0);
x_47 = lean_box(1);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Name_toString(x_44, x_48, x_46);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_mk_string_unchecked(":", 1, 1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("block_", 6, 6);
x_55 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_6 = x_58;
goto block_16;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_mk_string_unchecked(" -> ", 4, 4);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_4);
lean_dec(x_4);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_1 = x_14;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
x_2 = x_13;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
x_2 = x_13;
goto block_12;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_15);
x_20 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(x_14, x_19, x_20, x_13);
x_2 = x_21;
goto block_12;
}
}
block_12:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("{", 1, 1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("}", 1, 1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_instToFormatParamMap() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_fmt___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Borrow_instToStringParamMap() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_instToStringParamMap___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_IR_IRType_isObj(x_9);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_usize_of_nat(x_3);
x_5 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_2);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_IR_Borrow_ParamMap_getHash(x_4);
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
x_29 = l_Lean_IR_Borrow_ParamMap_getHash(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_2, x_7);
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
x_13 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_17, x_6);
x_7 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_1);
x_20 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_19, x_6);
x_7 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; lean_object* x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_5);
x_18 = lean_array_get_size(x_15);
x_19 = l_Lean_IR_Borrow_ParamMap_getHash(x_16);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_unsigned_to_nat(16u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_sub(x_29, x_31);
x_33 = lean_usize_land(x_28, x_32);
x_34 = lean_array_uget(x_15, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_16, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_nat_add(x_14, x_30);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_17);
lean_ctor_set(x_37, 2, x_34);
x_38 = lean_array_uset(x_15, x_33, x_37);
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
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_38);
lean_ctor_set(x_3, 1, x_45);
lean_ctor_set(x_3, 0, x_36);
x_8 = x_3;
goto block_12;
}
else
{
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_36);
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_box(0);
x_47 = lean_array_uset(x_15, x_33, x_46);
x_48 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_16, x_17, x_34);
x_49 = lean_array_uset(x_47, x_33, x_48);
lean_ctor_set(x_3, 1, x_49);
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; size_t x_64; size_t x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
lean_inc(x_1);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_4);
x_53 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_5);
x_54 = lean_array_get_size(x_51);
x_55 = l_Lean_IR_Borrow_ParamMap_getHash(x_52);
x_56 = lean_unsigned_to_nat(32u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_unsigned_to_nat(16u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_xor(x_59, x_62);
x_64 = lean_uint64_to_usize(x_63);
x_65 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_usize_of_nat(x_66);
x_68 = lean_usize_sub(x_65, x_67);
x_69 = lean_usize_land(x_64, x_68);
x_70 = lean_array_uget(x_51, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_52, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_nat_add(x_50, x_66);
lean_dec(x_50);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_52);
lean_ctor_set(x_73, 1, x_53);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_51, x_69, x_73);
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
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_8 = x_82;
goto block_12;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_74);
x_8 = x_83;
goto block_12;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_51, x_69, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_52, x_53, x_70);
x_87 = lean_array_uset(x_85, x_69, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_50);
lean_ctor_set(x_88, 1, x_87);
x_8 = x_88;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_6, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_10;
goto _start;
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_2, 3);
lean_inc(x_89);
lean_dec(x_2);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get_size(x_89);
x_92 = lean_box(0);
x_93 = lean_nat_dec_lt(x_90, x_91);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_3);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_91, x_91);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_3);
return x_96;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; 
x_97 = lean_usize_of_nat(x_90);
x_98 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_99 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(x_1, x_89, x_97, x_98, x_92, x_3);
lean_dec(x_89);
return x_99;
}
}
}
default: 
{
uint8_t x_100; 
x_100 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_100 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_101);
lean_dec(x_2);
x_2 = x_101;
goto _start;
}
case 1:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_2, 3);
lean_inc(x_103);
lean_dec(x_2);
x_2 = x_103;
goto _start;
}
case 2:
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_2, 3);
lean_inc(x_105);
lean_dec(x_2);
x_2 = x_105;
goto _start;
}
case 3:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_dec(x_2);
x_2 = x_107;
goto _start;
}
case 4:
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_2, 3);
lean_inc(x_109);
lean_dec(x_2);
x_2 = x_109;
goto _start;
}
case 5:
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_2, 5);
lean_inc(x_111);
lean_dec(x_2);
x_2 = x_111;
goto _start;
}
case 6:
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_2, 2);
lean_inc(x_113);
lean_dec(x_2);
x_2 = x_113;
goto _start;
}
case 7:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_2, 2);
lean_inc(x_115);
lean_dec(x_2);
x_2 = x_115;
goto _start;
}
case 8:
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_2, 1);
lean_inc(x_117);
lean_dec(x_2);
x_2 = x_117;
goto _start;
}
case 9:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_2 = x_119;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_3);
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 3);
lean_inc(x_18);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_1);
x_27 = l_Lean_isExport(x_1, x_16);
lean_inc(x_16);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_16);
x_29 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_27, x_17);
x_30 = lean_array_get_size(x_26);
x_31 = l_Lean_IR_Borrow_ParamMap_getHash(x_28);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_26, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_28, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_nat_add(x_25, x_42);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_29);
lean_ctor_set(x_49, 2, x_46);
x_50 = lean_array_uset(x_26, x_45, x_49);
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
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_50);
lean_ctor_set(x_6, 1, x_57);
lean_ctor_set(x_6, 0, x_48);
x_19 = x_6;
goto block_23;
}
else
{
lean_ctor_set(x_6, 1, x_50);
lean_ctor_set(x_6, 0, x_48);
x_19 = x_6;
goto block_23;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_box(0);
x_59 = lean_array_uset(x_26, x_45, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_28, x_29, x_46);
x_61 = lean_array_uset(x_59, x_45, x_60);
lean_ctor_set(x_6, 1, x_61);
x_19 = x_6;
goto block_23;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; size_t x_77; size_t x_78; lean_object* x_79; size_t x_80; size_t x_81; size_t x_82; lean_object* x_83; uint8_t x_84; 
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_6);
lean_inc(x_16);
lean_inc(x_1);
x_64 = l_Lean_isExport(x_1, x_16);
lean_inc(x_16);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_16);
x_66 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_64, x_17);
x_67 = lean_array_get_size(x_63);
x_68 = l_Lean_IR_Borrow_ParamMap_getHash(x_65);
x_69 = lean_unsigned_to_nat(32u);
x_70 = lean_uint64_of_nat(x_69);
x_71 = lean_uint64_shift_right(x_68, x_70);
x_72 = lean_uint64_xor(x_68, x_71);
x_73 = lean_unsigned_to_nat(16u);
x_74 = lean_uint64_of_nat(x_73);
x_75 = lean_uint64_shift_right(x_72, x_74);
x_76 = lean_uint64_xor(x_72, x_75);
x_77 = lean_uint64_to_usize(x_76);
x_78 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_usize_of_nat(x_79);
x_81 = lean_usize_sub(x_78, x_80);
x_82 = lean_usize_land(x_77, x_81);
x_83 = lean_array_uget(x_63, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_65, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_nat_add(x_62, x_79);
lean_dec(x_62);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_66);
lean_ctor_set(x_86, 2, x_83);
x_87 = lean_array_uset(x_63, x_82, x_86);
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_nat_shiftl(x_85, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_div(x_89, x_90);
lean_dec(x_89);
x_92 = lean_array_get_size(x_87);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_94);
x_19 = x_95;
goto block_23;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_87);
x_19 = x_96;
goto block_23;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_box(0);
x_98 = lean_array_uset(x_63, x_82, x_97);
x_99 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_65, x_66, x_83);
x_100 = lean_array_uset(x_98, x_82, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_62);
lean_ctor_set(x_101, 1, x_100);
x_19 = x_101;
goto block_23;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_16, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_7 = x_21;
x_8 = x_22;
goto block_13;
}
}
else
{
lean_object* x_102; 
lean_dec(x_15);
x_102 = lean_box(0);
x_7 = x_102;
x_8 = x_6;
goto block_13;
}
}
else
{
lean_object* x_103; 
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_5);
lean_ctor_set(x_103, 1, x_6);
return x_103;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(x_1, x_2, x_11, x_12, x_6, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_13 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_206_(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedFnBody;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_19 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_18);
lean_ctor_set(x_7, 1, x_19);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_1);
x_22 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_10 = x_23;
goto block_16;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_1);
x_26 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_25);
lean_ctor_set(x_7, 0, x_26);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
lean_inc(x_1);
x_28 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_10 = x_29;
goto block_16;
}
}
block_16:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_14 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_array_get_size(x_15);
x_18 = l_Lean_IR_Borrow_ParamMap_getHash(x_16);
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
x_33 = lean_array_uget(x_15, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_16, x_33);
lean_dec(x_33);
lean_dec(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_36 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitFnBody", 40, 40);
x_37 = lean_unsigned_to_nat(114u);
x_38 = lean_unsigned_to_nat(17u);
x_39 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
lean_inc(x_1);
x_43 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_12);
x_44 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_13);
lean_ctor_set(x_3, 3, x_44);
lean_ctor_set(x_3, 2, x_43);
lean_ctor_set(x_3, 1, x_42);
return x_3;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; lean_object* x_62; size_t x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_inc(x_1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_array_get_size(x_48);
x_51 = l_Lean_IR_Borrow_ParamMap_getHash(x_49);
x_52 = lean_unsigned_to_nat(32u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_unsigned_to_nat(16u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_usize_of_nat(x_62);
x_64 = lean_usize_sub(x_61, x_63);
x_65 = lean_usize_land(x_60, x_64);
x_66 = lean_array_uget(x_48, x_65);
x_67 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_49, x_66);
lean_dec(x_66);
lean_dec(x_49);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
x_68 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_69 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitFnBody", 40, 40);
x_70 = lean_unsigned_to_nat(114u);
x_71 = lean_unsigned_to_nat(17u);
x_72 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_73 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_74 = l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
lean_inc(x_1);
x_76 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_46);
x_77 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_47);
x_78 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_78, 0, x_45);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
return x_78;
}
}
}
case 10:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_3, 3);
x_81 = lean_array_size(x_80);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_usize_of_nat(x_82);
x_84 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_81, x_83, x_80);
lean_ctor_set(x_3, 3, x_84);
return x_3;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; lean_object* x_90; size_t x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_3, 0);
x_86 = lean_ctor_get(x_3, 1);
x_87 = lean_ctor_get(x_3, 2);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_3);
x_89 = lean_array_size(x_88);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_usize_of_nat(x_90);
x_92 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_89, x_91, x_88);
x_93 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_92);
return x_93;
}
}
default: 
{
uint8_t x_94; 
x_94 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_94 == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_3, 3);
lean_inc(x_95);
x_4 = x_95;
goto block_9;
}
case 1:
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_3, 3);
lean_inc(x_96);
x_4 = x_96;
goto block_9;
}
case 2:
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_3, 3);
lean_inc(x_97);
x_4 = x_97;
goto block_9;
}
case 3:
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_3, 2);
lean_inc(x_98);
x_4 = x_98;
goto block_9;
}
case 4:
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_3, 3);
lean_inc(x_99);
x_4 = x_99;
goto block_9;
}
case 5:
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_3, 5);
lean_inc(x_100);
x_4 = x_100;
goto block_9;
}
case 6:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_3, 2);
lean_inc(x_101);
x_4 = x_101;
goto block_9;
}
case 7:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
x_4 = x_102;
goto block_9;
}
case 8:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_3, 1);
lean_inc(x_103);
x_4 = x_103;
goto block_9;
}
case 9:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_3, 1);
lean_inc(x_104);
x_4 = x_104;
goto block_9;
}
default: 
{
lean_inc(x_3);
x_4 = x_3;
goto block_9;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(13);
x_6 = l_Lean_IR_FnBody_setBody(x_3, x_5);
x_7 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_4);
x_8 = l_Lean_IR_FnBody_setBody(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = lean_array_get_size(x_22);
x_25 = l_Lean_IR_Borrow_ParamMap_getHash(x_23);
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
x_41 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_23, x_40);
lean_dec(x_40);
lean_dec(x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_6);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_42 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_43 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitDecls", 39, 39);
x_44 = lean_unsigned_to_nat(130u);
x_45 = lean_unsigned_to_nat(19u);
x_46 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_47 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
x_48 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_47);
x_9 = x_48;
goto block_15;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
lean_inc(x_17);
x_50 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_17, x_1, x_19);
lean_ctor_set(x_6, 3, x_50);
lean_ctor_set(x_6, 1, x_49);
x_9 = x_6;
goto block_15;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; size_t x_67; size_t x_68; lean_object* x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 2);
x_53 = lean_ctor_get(x_6, 3);
x_54 = lean_ctor_get(x_6, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_57 = lean_array_get_size(x_55);
x_58 = l_Lean_IR_Borrow_ParamMap_getHash(x_56);
x_59 = lean_unsigned_to_nat(32u);
x_60 = lean_uint64_of_nat(x_59);
x_61 = lean_uint64_shift_right(x_58, x_60);
x_62 = lean_uint64_xor(x_58, x_61);
x_63 = lean_unsigned_to_nat(16u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_uint64_shift_right(x_62, x_64);
x_66 = lean_uint64_xor(x_62, x_65);
x_67 = lean_uint64_to_usize(x_66);
x_68 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_usize_of_nat(x_69);
x_71 = lean_usize_sub(x_68, x_70);
x_72 = lean_usize_land(x_67, x_71);
x_73 = lean_array_uget(x_55, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_56, x_73);
lean_dec(x_73);
lean_dec(x_56);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_75 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_76 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitDecls", 39, 39);
x_77 = lean_unsigned_to_nat(130u);
x_78 = lean_unsigned_to_nat(19u);
x_79 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_80 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_75, x_76, x_77, x_78, x_79);
lean_dec(x_79);
lean_dec(x_76);
lean_dec(x_75);
x_81 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_80);
x_9 = x_81;
goto block_15;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
lean_dec(x_74);
lean_inc(x_51);
x_83 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_51, x_1, x_53);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_51);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_52);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_54);
x_9 = x_84;
goto block_15;
}
}
}
else
{
x_9 = x_6;
goto block_15;
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(x_2, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_applyParamMap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_getCurrFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(1);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_markModified___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_markModified___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_markModified(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_Borrow_getCurrFn(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_ctor_set(x_4, 1, x_1);
x_9 = l_Lean_IR_Borrow_OwnedSet_contains(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box(1);
x_11 = l_Lean_IR_Borrow_OwnedSet_insert(x_8, x_4);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Lean_IR_Borrow_OwnedSet_contains(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_box(1);
x_24 = l_Lean_IR_Borrow_OwnedSet_insert(x_20, x_21);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Borrow_ownVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_Borrow_ownArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(x_1, x_11, x_12, x_6, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_Borrow_getCurrFn(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_ctor_set(x_4, 1, x_1);
x_8 = l_Lean_IR_Borrow_OwnedSet_contains(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_Lean_IR_Borrow_OwnedSet_contains(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_isOwned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_19; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_19 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
if (x_19 == 0)
{
x_11 = x_8;
x_12 = x_5;
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_inc(x_20);
x_21 = l_Lean_IR_Borrow_isOwned(x_20, x_4, x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_11 = x_8;
x_12 = x_24;
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_IR_Borrow_markModified___redArg(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_31);
x_11 = x_30;
x_12 = x_27;
goto block_18;
}
}
block_18:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
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
x_24 = lean_array_uget(x_6, x_23);
lean_dec(x_6);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_4);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_size(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_usize_of_nat(x_29);
x_31 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_28, x_30, x_27, x_2, x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_box(0);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
lean_dec(x_32);
x_46 = lean_array_get_size(x_38);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = lean_usize_sub(x_47, x_21);
x_49 = lean_usize_land(x_18, x_48);
x_50 = lean_array_uget(x_38, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_nat_add(x_37, x_20);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_34);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_array_uset(x_38, x_49, x_53);
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
lean_object* x_61; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_54);
lean_ctor_set(x_33, 1, x_61);
lean_ctor_set(x_33, 0, x_52);
x_42 = x_33;
goto block_45;
}
else
{
lean_ctor_set(x_33, 1, x_54);
lean_ctor_set(x_33, 0, x_52);
x_42 = x_33;
goto block_45;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = lean_array_uset(x_38, x_49, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_34, x_50);
x_65 = lean_array_uset(x_63, x_49, x_64);
lean_ctor_set(x_33, 1, x_65);
x_42 = x_33;
goto block_45;
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_35)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_35;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_75; size_t x_76; size_t x_77; size_t x_78; lean_object* x_79; uint8_t x_80; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_box(0);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
lean_dec(x_32);
x_75 = lean_array_get_size(x_67);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_77 = lean_usize_sub(x_76, x_21);
x_78 = lean_usize_land(x_18, x_77);
x_79 = lean_array_uget(x_67, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_81 = lean_nat_add(x_66, x_20);
lean_dec(x_66);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_34);
lean_ctor_set(x_82, 2, x_79);
x_83 = lean_array_uset(x_67, x_78, x_82);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_nat_shiftl(x_81, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_71 = x_91;
goto block_74;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_83);
x_71 = x_92;
goto block_74;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_67, x_78, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_34, x_79);
x_96 = lean_array_uset(x_94, x_78, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_66);
lean_ctor_set(x_97, 1, x_96);
x_71 = x_97;
goto block_74;
}
block_74:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_70);
if (lean_is_scalar(x_35)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_35;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint64_t x_100; lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; size_t x_109; size_t x_110; lean_object* x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_4, 1);
lean_inc(x_98);
lean_dec(x_4);
x_99 = lean_array_get_size(x_98);
x_100 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
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
x_116 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_115);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_3);
return x_118;
}
else
{
lean_object* x_119; size_t x_120; lean_object* x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_138; size_t x_139; size_t x_140; size_t x_141; lean_object* x_142; uint8_t x_143; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_array_size(x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_usize_of_nat(x_121);
x_123 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_120, x_122, x_119, x_2, x_3);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_124, sizeof(void*)*2);
lean_dec(x_124);
x_138 = lean_array_get_size(x_129);
x_139 = lean_usize_of_nat(x_138);
lean_dec(x_138);
x_140 = lean_usize_sub(x_139, x_112);
x_141 = lean_usize_land(x_109, x_140);
x_142 = lean_array_uget(x_129, x_141);
x_143 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_144 = lean_nat_add(x_128, x_111);
lean_dec(x_128);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_126);
lean_ctor_set(x_145, 2, x_142);
x_146 = lean_array_uset(x_129, x_141, x_145);
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_nat_shiftl(x_144, x_147);
x_149 = lean_unsigned_to_nat(3u);
x_150 = lean_nat_div(x_148, x_149);
lean_dec(x_148);
x_151 = lean_array_get_size(x_146);
x_152 = lean_nat_dec_le(x_150, x_151);
lean_dec(x_151);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_146);
if (lean_is_scalar(x_130)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_130;
}
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_153);
x_134 = x_154;
goto block_137;
}
else
{
lean_object* x_155; 
if (lean_is_scalar(x_130)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_130;
}
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_146);
x_134 = x_155;
goto block_137;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_box(0);
x_157 = lean_array_uset(x_129, x_141, x_156);
x_158 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_126, x_142);
x_159 = lean_array_uset(x_157, x_141, x_158);
if (lean_is_scalar(x_130)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_130;
}
lean_ctor_set(x_160, 0, x_128);
lean_ctor_set(x_160, 1, x_159);
x_134 = x_160;
goto block_137;
}
block_137:
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_127;
}
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_updateParamMap(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_7, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_7, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_4 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__0), 5, 0);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__1), 5, 0);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__2), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__3), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set(x_21, 3, x_5);
lean_ctor_set(x_21, 4, x_4);
x_22 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_instInhabited(lean_box(0));
x_25 = l_instInhabitedOfMonad___redArg(x_23, x_24);
x_26 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_apply_2(x_27, x_2, x_3);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
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
x_24 = lean_array_uget(x_6, x_23);
lean_dec(x_6);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ir_find_env_decl(x_27, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_4);
x_29 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_30 = lean_mk_string_unchecked("Lean.IR.Borrow.getParamInfo", 27, 27);
x_31 = lean_unsigned_to_nat(203u);
x_32 = lean_unsigned_to_nat(21u);
x_33 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_34, x_2, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_37);
return x_4;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_4);
lean_dec(x_1);
x_38 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_39 = lean_mk_string_unchecked("Lean.IR.Borrow.getParamInfo", 27, 27);
x_40 = lean_unsigned_to_nat(204u);
x_41 = lean_unsigned_to_nat(11u);
x_42 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_43 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
x_44 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_43, x_2, x_3);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec(x_25);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_45);
return x_4;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; lean_object* x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_dec(x_4);
x_47 = lean_array_get_size(x_46);
x_48 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
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
x_63 = lean_array_uget(x_46, x_62);
lean_dec(x_46);
x_64 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ir_find_env_decl(x_66, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_69 = lean_mk_string_unchecked("Lean.IR.Borrow.getParamInfo", 27, 27);
x_70 = lean_unsigned_to_nat(203u);
x_71 = lean_unsigned_to_nat(21u);
x_72 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_73 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_74 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_73, x_2, x_3);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_2);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_3);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_1);
x_78 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
x_79 = lean_mk_string_unchecked("Lean.IR.Borrow.getParamInfo", 27, 27);
x_80 = lean_unsigned_to_nat(204u);
x_81 = lean_unsigned_to_nat(11u);
x_82 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_83 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_78, x_79, x_80, x_81, x_82);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
x_84 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_83, x_2, x_3);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_64, 0);
lean_inc(x_85);
lean_dec(x_64);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_IR_instInhabitedParam;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_array_get(x_11, x_1, x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget(x_2, x_15);
lean_dec(x_15);
x_19 = l_Lean_IR_Borrow_ownArg(x_18, x_5, x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_4 = x_13;
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_15);
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_2, x_1, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownArgsUsingParams(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_nat_sub(x_3, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = lean_array_fget(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_Borrow_isOwned(x_16, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_4 = x_12;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_IR_instInhabitedParam;
x_24 = lean_array_get(x_23, x_2, x_14);
lean_dec(x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_IR_Borrow_ownVar(x_25, x_5, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_4 = x_12;
x_6 = x_27;
goto _start;
}
}
else
{
lean_dec(x_14);
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 3);
x_19 = l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0(lean_box(0), x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_box(0);
x_8 = x_20;
x_9 = x_7;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
x_21 = l_Lean_IR_Borrow_ownVar(x_17, x_6, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_14;
}
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
x_8 = x_24;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(x_2, x_1, x_11, x_12, x_6, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgsIfParam(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_Borrow_ownArgsIfParam(x_5, x_3, x_7);
lean_dec(x_3);
lean_dec(x_5);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_Borrow_ownVar(x_9, x_3, x_11);
lean_dec(x_3);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_Borrow_ownVar(x_13, x_3, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_IR_Borrow_ownArgsIfParam(x_14, x_3, x_18);
lean_dec(x_3);
lean_dec(x_14);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_20);
x_35 = l_Lean_IR_Borrow_isOwned(x_20, x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_21 = x_3;
x_22 = x_38;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_1);
x_40 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_21 = x_3;
x_22 = x_41;
goto block_34;
}
block_34:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_IR_Borrow_isOwned(x_1, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_IR_Borrow_ownVar(x_20, x_21, x_32);
lean_dec(x_21);
return x_33;
}
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
lean_inc(x_3);
x_45 = l_Lean_IR_Borrow_getParamInfo(x_44, x_3, x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_IR_Borrow_ownArgsUsingParams(x_43, x_46, x_3, x_49);
lean_dec(x_3);
lean_dec(x_46);
lean_dec(x_43);
return x_50;
}
case 7:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_IR_Borrow_ownArgs(x_51, x_3, x_53);
lean_dec(x_3);
lean_dec(x_51);
return x_54;
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_IR_Borrow_ownVar(x_55, x_3, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_IR_Borrow_ownArgs(x_56, x_3, x_60);
lean_dec(x_3);
lean_dec(x_56);
return x_61;
}
default: 
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_4);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
x_25 = lean_name_eq(x_24, x_10);
lean_dec(x_24);
if (x_25 == 0)
{
x_13 = x_25;
goto block_21;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_1, x_23);
x_13 = x_26;
goto block_21;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_6 = x_5;
goto block_9;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_6 = x_5;
goto block_9;
}
block_21:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_14 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_12;
 lean_ctor_set_tag(x_15, 0);
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_10);
lean_inc(x_4);
x_17 = l_Lean_IR_Borrow_getParamInfo(x_16, x_4, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_11, x_18, x_4, x_19);
lean_dec(x_4);
lean_dec(x_18);
lean_dec(x_11);
return x_20;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
x_6 = x_5;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_preserveTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_4, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_6);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_usize_of_nat(x_7);
x_14 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(x_2, x_13, x_14, x_6);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_updateParamSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_5);
x_18 = l_Lean_IR_Borrow_collectFnBody(x_17, x_5, x_6);
x_7 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_5);
x_20 = l_Lean_IR_Borrow_collectFnBody(x_19, x_5, x_6);
x_7 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_7 = l_Lean_IR_Borrow_collectFnBody(x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_IR_Borrow_collectExpr(x_4, x_5, x_2, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_Borrow_preserveTailCall(x_4, x_5, x_6, x_2, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_2);
x_16 = l_Lean_IR_Borrow_updateParamSet(x_2, x_13);
lean_dec(x_13);
x_17 = l_Lean_IR_Borrow_collectFnBody(x_14, x_16, x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 0, x_21);
x_22 = l_Lean_IR_Borrow_updateParamMap(x_17, x_2, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_1 = x_15;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
x_28 = l_Lean_IR_Borrow_updateParamMap(x_27, x_2, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_1 = x_15;
x_3 = x_29;
goto _start;
}
}
case 10:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_31);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_33, x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_32);
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(x_31, x_39, x_40, x_34, x_2, x_3);
lean_dec(x_31);
return x_41;
}
}
}
case 12:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_43);
lean_ctor_set(x_1, 0, x_45);
lean_inc(x_2);
x_46 = l_Lean_IR_Borrow_getParamInfo(x_1, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_IR_Borrow_ownArgsUsingParams(x_44, x_47, x_2, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_44, x_47, x_2, x_50);
lean_dec(x_2);
lean_dec(x_47);
lean_dec(x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
lean_inc(x_2);
x_56 = l_Lean_IR_Borrow_getParamInfo(x_55, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_IR_Borrow_ownArgsUsingParams(x_53, x_57, x_2, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_53, x_57, x_2, x_60);
lean_dec(x_2);
lean_dec(x_57);
lean_dec(x_53);
return x_61;
}
}
default: 
{
uint8_t x_62; 
x_62 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_62 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_dec(x_1);
x_1 = x_63;
goto _start;
}
case 1:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
lean_dec(x_1);
x_1 = x_65;
goto _start;
}
case 2:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
lean_dec(x_1);
x_1 = x_67;
goto _start;
}
case 3:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
lean_dec(x_1);
x_1 = x_69;
goto _start;
}
case 4:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_1, 3);
lean_inc(x_71);
lean_dec(x_1);
x_1 = x_71;
goto _start;
}
case 5:
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_1, 5);
lean_inc(x_73);
lean_dec(x_1);
x_1 = x_73;
goto _start;
}
case 6:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
lean_dec(x_1);
x_1 = x_75;
goto _start;
}
case 7:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_77);
lean_dec(x_1);
x_1 = x_77;
goto _start;
}
case 8:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_dec(x_1);
x_1 = x_79;
goto _start;
}
case 9:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_1 = x_81;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_Borrow_updateParamSet(x_2, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_4);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_10);
lean_inc(x_11);
x_12 = l_Lean_IR_Borrow_collectFnBody(x_6, x_11, x_3);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = l_Lean_IR_Borrow_updateParamMap(x_14, x_11, x_13);
lean_dec(x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_whileModifing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_free_object(x_9);
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_IR_Borrow_collectDecl(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_2, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_1);
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(x_3, x_11, x_12, x_6, x_4, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_collectDecls___lam__0___boxed), 5, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_IR_Borrow_whileModifing(x_6, x_1, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_collectDecls___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
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
x_17 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
x_20 = l_Lean_IR_Borrow_collectDecls(x_5, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_6 = l_Lean_IR_Borrow_infer(x_5, x_1);
x_7 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
x_10 = l_Lean_IR_Borrow_infer(x_8, x_1);
x_11 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_inferBorrow___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_inferBorrow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Borrow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ExportAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Borrow_OwnedSet_instBEqKey = _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instBEqKey);
l_Lean_IR_Borrow_OwnedSet_instHashableKey = _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instHashableKey);
l_Lean_IR_Borrow_ParamMap_instBEqKey = _init_l_Lean_IR_Borrow_ParamMap_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instBEqKey);
l_Lean_IR_Borrow_ParamMap_instHashableKey = _init_l_Lean_IR_Borrow_ParamMap_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instHashableKey);
l_Lean_IR_Borrow_instToFormatParamMap = _init_l_Lean_IR_Borrow_instToFormatParamMap();
lean_mark_persistent(l_Lean_IR_Borrow_instToFormatParamMap);
l_Lean_IR_Borrow_instToStringParamMap = _init_l_Lean_IR_Borrow_instToStringParamMap();
lean_mark_persistent(l_Lean_IR_Borrow_instToStringParamMap);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
