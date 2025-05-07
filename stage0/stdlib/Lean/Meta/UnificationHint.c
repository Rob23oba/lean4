// Lean compiler output
// Module: Lean.Meta.UnificationHint
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.Basic Lean.Meta.DiscrTree Lean.Meta.SynthInstance
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
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_exceptBoolEmoji(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints;
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_format(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112____boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unificationHintExtension;
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHints;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedUnificationHintEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_instToFormatName__lean;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2243_(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHintEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedUnificationHints() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DiscrTree_format(lean_box(0), x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatUnificationHints() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToFormatName__lean;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatUnificationHints___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatUnificationHints___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instToFormatUnificationHints___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_box(1);
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
x_23 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 17, x_24);
x_25 = l_Lean_Meta_Config_toConfigWithKey(x_6);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_name_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_nat_add(x_6, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_shiftr(x_9, x_10);
lean_dec(x_9);
x_12 = lean_array_fget(x_4, x_11);
x_13 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_12, x_5);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_5, x_12);
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
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_2, x_3, x_22, x_18);
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
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_2, x_3, x_28, x_25);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_2, x_3, x_10, x_7);
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
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_2, x_3, x_14, x_12);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(x_5, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(x_10, x_5);
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
x_16 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
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
x_21 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(x_20, x_5);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(x_5, x_20);
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
x_26 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
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
x_28 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_19);
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
x_32 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
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
x_35 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_34);
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
x_40 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
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
x_43 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_42);
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
x_47 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_46);
x_48 = lean_array_push(x_4, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0(x_6, x_2);
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
x_15 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_7, x_14);
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
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__0(x_17, x_2);
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
x_28 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_18, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_2, x_3, x_13, x_12);
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
x_22 = l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__5(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_UnificationHints_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_UnificationHints_add_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Meta", 4, 4);
x_5 = lean_mk_string_unchecked("unificationHintExtension", 24, 24);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_UnificationHints_add), 2, 0);
x_8 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_2);
x_10 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_112_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_mk_string_unchecked("invalid unification hint constraint, unexpected term", 52, 52);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = l_Lean_Expr_hasLooseBVars(x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_5);
lean_dec(x_1);
x_12 = lean_array_push(x_2, x_10);
x_1 = x_4;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_mk_string_unchecked("invalid unification hint constraint, unexpected dependency", 58, 58);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_indentExpr(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_Expr_hasLooseBVars(x_4);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_array_push(x_2, x_21);
x_1 = x_4;
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_mk_string_unchecked("invalid unification hint constraint, unexpected dependency", 58, 58);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_indentExpr(x_1);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(x_1);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_array_to_list(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_array_to_list(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_Meta_isExprDefEq(x_12, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_mk_string_unchecked("invalid unification hint, failed to unify constraint left-hand-side", 67, 67);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_indentExpr(x_12);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_19);
x_21 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_13);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_28, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_1 = x_11;
x_6 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_39);
lean_inc(x_38);
x_40 = l_Lean_Meta_isExprDefEq(x_38, x_39, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("invalid unification hint, failed to unify constraint left-hand-side", 67, 67);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_indentExpr(x_38);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_39);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_55, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_38);
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_1 = x_37;
x_6 = x_57;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_61 = x_40;
} else {
 lean_dec_ref(x_40);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_Meta_isExprDefEq(x_12, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_mk_string_unchecked("invalid unification hint, failed to unify constraint left-hand-side", 67, 67);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_indentExpr(x_12);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_19);
x_21 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_13);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_28, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(x_11, x_2, x_3, x_4, x_5, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_39);
lean_inc(x_38);
x_40 = l_Lean_Meta_isExprDefEq(x_38, x_39, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("invalid unification hint, failed to unify constraint left-hand-side", 67, 67);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_indentExpr(x_38);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_39);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_55, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_39);
lean_dec(x_38);
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_58 = l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(x_37, x_2, x_3, x_4, x_5, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_61 = x_40;
} else {
 lean_dec_ref(x_40);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_Meta_isExprDefEq(x_13, x_14, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_mk_string_unchecked("invalid unification hint, failed to unify pattern left-hand-side", 64, 64);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_20);
x_22 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_14);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_15, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
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
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_44);
lean_inc(x_43);
x_45 = l_Lean_Meta_isExprDefEq(x_43, x_44, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_mk_string_unchecked("invalid unification hint, failed to unify pattern left-hand-side", 64, 64);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = l_Lean_indentExpr(x_43);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_mk_string_unchecked("\nwith right-hand-side", 21, 21);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_indentExpr(x_44);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("", 0, 0);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_60, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_63 = x_45;
} else {
 lean_dec_ref(x_45);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_45, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_45, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_68 = x_45;
} else {
 lean_dec_ref(x_45);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at___List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at_____private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_ConstantInfo_value_x3f(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("invalid unification hint, it must be a definition", 49, 49);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
lean_inc(x_3);
x_19 = l_Lean_Meta_lambdaMetaTelescope(x_17, x_18, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_25, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 6);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_42 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set_uint64(x_42, sizeof(void*)*7, x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 9, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 10, x_41);
x_43 = lean_unbox(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Meta_DiscrTree_mkPath(x_30, x_43, x_42, x_4, x_5, x_6, x_22);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(x_27, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_3);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_unificationHintExtension;
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 0, x_45);
x_52 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(x_51, x_47, x_2, x_4, x_5, x_6, x_49);
lean_dec(x_6);
lean_dec(x_4);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = l_Lean_Meta_unificationHintExtension;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_1);
x_56 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(x_54, x_55, x_2, x_4, x_5, x_6, x_53);
lean_dec(x_6);
lean_dec(x_4);
return x_56;
}
}
else
{
lean_dec(x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_47;
}
}
else
{
uint8_t x_57; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
return x_8;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_addUnificationHint___lam__0___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_9, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addUnificationHint___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addUnificationHint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addUnificationHint(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_nat_pow(x_11, x_14);
lean_dec(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_10);
lean_inc(x_10);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_10);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_10);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_10);
lean_inc(x_10);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
lean_inc(x_10);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_10);
lean_inc(x_21);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
lean_ctor_set(x_27, 8, x_26);
lean_inc(x_10);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_10);
lean_inc(x_10);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_10);
lean_inc(x_10);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_10);
lean_inc(x_10);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_10);
lean_inc(x_31);
lean_inc(x_28);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_31);
lean_inc(x_18);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_18);
lean_inc(x_18);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_20);
lean_ctor_set_usize(x_34, 4, x_13);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_10);
lean_inc_n(x_21, 2);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_9);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_st_mk_ref(x_37, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(1);
x_42 = lean_box(1);
x_43 = lean_box(0);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_10);
x_46 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_18);
lean_ctor_set(x_46, 2, x_20);
lean_ctor_set(x_46, 3, x_20);
lean_ctor_set_usize(x_46, 4, x_13);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 0, 18);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 0, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 1, x_50);
x_51 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 2, x_51);
x_52 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 3, x_52);
x_53 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 4, x_53);
x_54 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 5, x_54);
x_55 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 6, x_55);
x_56 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 7, x_56);
x_57 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 8, x_57);
x_58 = lean_unbox(x_42);
lean_ctor_set_uint8(x_48, 9, x_58);
x_59 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 10, x_59);
x_60 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 11, x_60);
x_61 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 12, x_61);
x_62 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 13, x_62);
x_63 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 14, x_63);
x_64 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 15, x_64);
x_65 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 16, x_65);
x_66 = lean_unbox(x_41);
lean_ctor_set_uint8(x_48, 17, x_66);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 2, x_9);
x_69 = lean_mk_empty_array_with_capacity(x_20);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_9);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_20);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_67);
x_73 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_73);
x_74 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_74);
x_75 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_75);
lean_inc(x_39);
x_76 = l_Lean_Meta_addUnificationHint(x_1, x_3, x_72, x_39, x_4, x_5, x_40);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_39, x_77);
lean_dec(x_39);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_dec(x_39);
return x_76;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_5);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = lean_mk_string_unchecked("UnificationHint", 15, 15);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("_hyg", 4, 4);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_unsigned_to_nat(809u);
x_20 = l_Lean_Name_num___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("unification_hint", 16, 16);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("unification hint", 16, 16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_26);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
x_28 = l_Lean_registerBuiltinAttribute(x_27, x_1);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_UnificationHint___hyg_809_(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_UnificationHint___hyg_809_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint8_t x_34; uint64_t x_35; uint64_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_8 = lean_box(2);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_ctor_get_uint8(x_9, 10);
x_20 = lean_ctor_get_uint8(x_9, 11);
x_21 = lean_ctor_get_uint8(x_9, 12);
x_22 = lean_ctor_get_uint8(x_9, 13);
x_23 = lean_ctor_get_uint8(x_9, 14);
x_24 = lean_ctor_get_uint8(x_9, 15);
x_25 = lean_ctor_get_uint8(x_9, 16);
x_26 = lean_ctor_get_uint8(x_9, 17);
x_27 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_27, 0, x_10);
lean_ctor_set_uint8(x_27, 1, x_11);
lean_ctor_set_uint8(x_27, 2, x_12);
lean_ctor_set_uint8(x_27, 3, x_13);
lean_ctor_set_uint8(x_27, 4, x_14);
lean_ctor_set_uint8(x_27, 5, x_15);
lean_ctor_set_uint8(x_27, 6, x_16);
lean_ctor_set_uint8(x_27, 7, x_17);
lean_ctor_set_uint8(x_27, 8, x_18);
x_28 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, 9, x_28);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_29 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_shift_left(x_32, x_31);
x_34 = lean_unbox(x_8);
x_35 = l_Lean_Meta_TransparencyMode_toUInt64(x_34);
x_36 = lean_uint64_lor(x_33, x_35);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get(x_3, 3);
x_41 = lean_ctor_get(x_3, 4);
x_42 = lean_ctor_get(x_3, 5);
x_43 = lean_ctor_get(x_3, 6);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
x_46 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set_uint64(x_46, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 8, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 9, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 10, x_45);
x_47 = lean_is_expr_def_eq(x_1, x_2, x_46, x_4, x_5, x_6, x_7);
return x_47;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_is_expr_def_eq(x_12, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_21; 
lean_free_object(x_14);
lean_dec(x_16);
x_21 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_21);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = lean_unbox(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_23);
x_29 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_29);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_24;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
}
}
else
{
uint8_t x_31; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = lean_is_expr_def_eq(x_37, x_38, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
x_44 = lean_unbox(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_40);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
x_1 = x_36;
x_2 = x_49;
x_7 = x_41;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_box(0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_array_fget(x_26, x_21);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_22);
x_32 = lean_box(3);
x_33 = lean_unbox(x_32);
x_34 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_28, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_31);
x_10 = x_35;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_37 = lean_infer_type(x_36, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_trySynthInstance(x_38, x_40, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_isExprDefEq(x_36, x_45, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
lean_ctor_set(x_42, 0, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_31);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
lean_ctor_set(x_42, 0, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_31);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
lean_free_object(x_42);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_19);
lean_ctor_set(x_56, 1, x_31);
x_10 = x_56;
x_11 = x_55;
goto block_16;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_42);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_62 = l_Lean_Meta_isExprDefEq(x_36, x_61, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_31);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_63);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_19);
lean_ctor_set(x_71, 1, x_31);
x_10 = x_71;
x_11 = x_70;
goto block_16;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_41);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_41, 0);
lean_dec(x_77);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_31);
lean_ctor_set(x_41, 0, x_80);
return x_41;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_41, 1);
lean_inc(x_81);
lean_dec(x_41);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_31);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_41);
if (x_86 == 0)
{
return x_41;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_41, 0);
x_88 = lean_ctor_get(x_41, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_41);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_37);
if (x_90 == 0)
{
return x_37;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_37, 0);
x_92 = lean_ctor_get(x_37, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_37);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_24; lean_object* x_25; uint8_t x_29; lean_object* x_30; lean_object* x_39; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_10 = l_Lean_Meta_saveState___redArg(x_6, x_7, x_8, x_9);
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
x_43 = lean_st_ref_take(x_6, x_12);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_84; 
x_50 = lean_ctor_get(x_45, 4);
lean_dec(x_50);
x_51 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_45, 4, x_52);
x_53 = lean_st_ref_set(x_6, x_44, x_46);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_1);
x_84 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_ConstantInfo_levelParams(x_85);
x_88 = lean_box(0);
x_89 = l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(x_87, x_88, x_5, x_6, x_7, x_8, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Core_instantiateValueLevelParams(x_85, x_90, x_7, x_8, x_91);
lean_dec(x_85);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_box(0);
lean_inc(x_5);
x_96 = l_Lean_Meta_lambdaMetaTelescope(x_93, x_95, x_5, x_6, x_7, x_8, x_94);
lean_dec(x_93);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = x_99;
goto block_42;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_236; uint8_t x_237; uint64_t x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_159 = lean_ctor_get_uint8(x_105, 0);
x_160 = lean_ctor_get_uint8(x_105, 1);
x_161 = lean_ctor_get_uint8(x_105, 2);
x_162 = lean_ctor_get_uint8(x_105, 3);
x_163 = lean_ctor_get_uint8(x_105, 4);
x_164 = lean_box(0);
x_165 = lean_ctor_get_uint8(x_105, 6);
x_166 = lean_ctor_get_uint8(x_105, 7);
x_167 = lean_ctor_get_uint8(x_105, 8);
x_168 = lean_ctor_get_uint8(x_105, 9);
x_169 = lean_ctor_get_uint8(x_105, 10);
x_170 = lean_ctor_get_uint8(x_105, 11);
x_171 = lean_ctor_get_uint8(x_105, 12);
x_172 = lean_ctor_get_uint8(x_105, 13);
x_173 = lean_ctor_get_uint8(x_105, 14);
x_174 = lean_ctor_get_uint8(x_105, 15);
x_175 = lean_ctor_get_uint8(x_105, 16);
x_176 = lean_ctor_get_uint8(x_105, 17);
lean_dec(x_105);
x_177 = lean_mk_string_unchecked("Meta", 4, 4);
x_178 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_179 = lean_mk_string_unchecked("hint", 4, 4);
x_236 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_236, 0, x_159);
lean_ctor_set_uint8(x_236, 1, x_160);
lean_ctor_set_uint8(x_236, 2, x_161);
lean_ctor_set_uint8(x_236, 3, x_162);
lean_ctor_set_uint8(x_236, 4, x_163);
x_237 = lean_unbox(x_164);
lean_ctor_set_uint8(x_236, 5, x_237);
lean_ctor_set_uint8(x_236, 6, x_165);
lean_ctor_set_uint8(x_236, 7, x_166);
lean_ctor_set_uint8(x_236, 8, x_167);
lean_ctor_set_uint8(x_236, 9, x_168);
lean_ctor_set_uint8(x_236, 10, x_169);
lean_ctor_set_uint8(x_236, 11, x_170);
lean_ctor_set_uint8(x_236, 12, x_171);
lean_ctor_set_uint8(x_236, 13, x_172);
lean_ctor_set_uint8(x_236, 14, x_173);
lean_ctor_set_uint8(x_236, 15, x_174);
lean_ctor_set_uint8(x_236, 16, x_175);
lean_ctor_set_uint8(x_236, 17, x_176);
x_238 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_236);
x_239 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_240 = lean_ctor_get(x_5, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_5, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_5, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_5, 4);
lean_inc(x_243);
x_244 = lean_ctor_get(x_5, 5);
lean_inc(x_244);
x_245 = lean_ctor_get(x_5, 6);
lean_inc(x_245);
x_246 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_247 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_248 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_248, 0, x_236);
lean_ctor_set(x_248, 1, x_240);
lean_ctor_set(x_248, 2, x_241);
lean_ctor_set(x_248, 3, x_242);
lean_ctor_set(x_248, 4, x_243);
lean_ctor_set(x_248, 5, x_244);
lean_ctor_set(x_248, 6, x_245);
lean_ctor_set_uint64(x_248, sizeof(void*)*7, x_238);
lean_ctor_set_uint8(x_248, sizeof(void*)*7 + 8, x_239);
lean_ctor_set_uint8(x_248, sizeof(void*)*7 + 9, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*7 + 10, x_247);
x_249 = lean_ctor_get(x_106, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_251 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_250, x_2, x_248, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_3);
x_180 = x_251;
goto block_235;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_249, 1);
lean_inc(x_255);
lean_dec(x_249);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_256 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_255, x_3, x_248, x_6, x_7, x_8, x_254);
lean_dec(x_248);
x_180 = x_256;
goto block_235;
}
}
else
{
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_3);
x_180 = x_251;
goto block_235;
}
block_158:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_dec(x_106);
x_114 = lean_box(0);
x_115 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
x_117 = l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(x_113, x_116, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_117);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_117, 1);
x_122 = lean_ctor_get(x_117, 0);
lean_dec(x_122);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_array_get_size(x_101);
x_125 = l_Array_toSubarray___redArg(x_101, x_123, x_124);
lean_ctor_set(x_117, 1, x_125);
lean_ctor_set(x_117, 0, x_114);
x_126 = lean_array_size(x_100);
x_127 = lean_usize_of_nat(x_123);
x_128 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(x_100, x_126, x_127, x_117, x_108, x_109, x_110, x_111, x_121);
lean_dec(x_100);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_58 = x_107;
x_59 = x_131;
goto block_83;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
x_58 = x_134;
x_59 = x_132;
goto block_83;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 1);
lean_inc(x_136);
lean_dec(x_128);
x_24 = x_135;
x_25 = x_136;
goto block_28;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_117, 1);
lean_inc(x_137);
lean_dec(x_117);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_array_get_size(x_101);
x_140 = l_Array_toSubarray___redArg(x_101, x_138, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_114);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_array_size(x_100);
x_143 = lean_usize_of_nat(x_138);
x_144 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(x_100, x_142, x_143, x_141, x_108, x_109, x_110, x_111, x_137);
lean_dec(x_100);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_58 = x_107;
x_59 = x_147;
goto block_83;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
x_58 = x_150;
x_59 = x_148;
goto block_83;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
lean_dec(x_144);
x_24 = x_151;
x_25 = x_152;
goto block_28;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_100);
x_153 = lean_ctor_get(x_117, 1);
lean_inc(x_153);
lean_dec(x_117);
x_154 = lean_ctor_get(x_119, 0);
lean_inc(x_154);
lean_dec(x_119);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
x_58 = x_155;
x_59 = x_153;
goto block_83;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
x_156 = lean_ctor_get(x_117, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 1);
lean_inc(x_157);
lean_dec(x_117);
x_24 = x_156;
x_25 = x_157;
goto block_28;
}
}
block_235:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_39 = x_183;
goto block_42;
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_180);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_180, 1);
x_186 = lean_ctor_get(x_180, 0);
lean_dec(x_186);
x_187 = l_Lean_Name_mkStr3(x_177, x_178, x_179);
lean_inc(x_187);
x_188 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_187, x_5, x_6, x_7, x_8, x_185);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
lean_dec(x_187);
lean_free_object(x_180);
lean_dec(x_1);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_unbox(x_181);
lean_dec(x_181);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = x_192;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_191;
goto block_158;
}
else
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_188);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_194 = lean_ctor_get(x_188, 1);
x_195 = lean_ctor_get(x_188, 0);
lean_dec(x_195);
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_188, 7);
lean_ctor_set(x_188, 1, x_198);
lean_ctor_set(x_188, 0, x_197);
x_199 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
lean_ctor_set_tag(x_180, 7);
lean_ctor_set(x_180, 1, x_200);
lean_ctor_set(x_180, 0, x_188);
x_201 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_187, x_180, x_5, x_6, x_7, x_8, x_194);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_unbox(x_181);
lean_dec(x_181);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = x_203;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_202;
goto block_158;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
lean_dec(x_188);
x_205 = lean_mk_string_unchecked("", 0, 0);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = l_Lean_MessageData_ofName(x_1);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
x_210 = l_Lean_stringToMessageData(x_209);
lean_dec(x_209);
lean_ctor_set_tag(x_180, 7);
lean_ctor_set(x_180, 1, x_210);
lean_ctor_set(x_180, 0, x_208);
x_211 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_187, x_180, x_5, x_6, x_7, x_8, x_204);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_unbox(x_181);
lean_dec(x_181);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = x_213;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_212;
goto block_158;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_180, 1);
lean_inc(x_214);
lean_dec(x_180);
x_215 = l_Lean_Name_mkStr3(x_177, x_178, x_179);
lean_inc(x_215);
x_216 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_215, x_5, x_6, x_7, x_8, x_214);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
lean_dec(x_215);
lean_dec(x_1);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_unbox(x_181);
lean_dec(x_181);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = x_220;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_219;
goto block_158;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_221 = lean_ctor_get(x_216, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
x_223 = lean_mk_string_unchecked("", 0, 0);
x_224 = l_Lean_stringToMessageData(x_223);
lean_dec(x_223);
x_225 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_222)) {
 x_226 = lean_alloc_ctor(7, 2, 0);
} else {
 x_226 = x_222;
 lean_ctor_set_tag(x_226, 7);
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
x_228 = l_Lean_stringToMessageData(x_227);
lean_dec(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_215, x_229, x_5, x_6, x_7, x_8, x_221);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_unbox(x_181);
lean_dec(x_181);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = x_232;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_231;
goto block_158;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_233 = lean_ctor_get(x_180, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_180, 1);
lean_inc(x_234);
lean_dec(x_180);
x_24 = x_233;
x_25 = x_234;
goto block_28;
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_92, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_92, 1);
lean_inc(x_258);
lean_dec(x_92);
x_24 = x_257;
x_25 = x_258;
goto block_28;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_ctor_get(x_84, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_84, 1);
lean_inc(x_260);
lean_dec(x_84);
x_24 = x_259;
x_25 = x_260;
goto block_28;
}
block_83:
{
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_29 = x_58;
x_30 = x_59;
goto block_38;
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_box(0);
x_61 = lean_unbox(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_processPostponed(x_4, x_61, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_13);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_63);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Meta_SavedState_restore___redArg(x_11, x_6, x_8, x_65);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_11);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_60);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_11);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = l_Lean_Meta_getPostponed___redArg(x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_PersistentArray_append___redArg(x_56, x_73);
lean_dec(x_73);
x_76 = l_Lean_Meta_setPostponed(x_75, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_63);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_63);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_5);
x_81 = lean_ctor_get(x_62, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_62, 1);
lean_inc(x_82);
lean_dec(x_62);
x_24 = x_81;
x_25 = x_82;
goto block_28;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_298; 
x_261 = lean_ctor_get(x_45, 0);
x_262 = lean_ctor_get(x_45, 1);
x_263 = lean_ctor_get(x_45, 2);
x_264 = lean_ctor_get(x_45, 3);
x_265 = lean_ctor_get(x_45, 5);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_45);
x_266 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_268, 0, x_261);
lean_ctor_set(x_268, 1, x_262);
lean_ctor_set(x_268, 2, x_263);
lean_ctor_set(x_268, 3, x_264);
lean_ctor_set(x_268, 4, x_267);
lean_ctor_set(x_268, 5, x_265);
lean_ctor_set(x_44, 1, x_268);
x_269 = lean_st_ref_set(x_6, x_44, x_46);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = l_Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_1);
x_298 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_5, x_6, x_7, x_8, x_273);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = l_Lean_ConstantInfo_levelParams(x_299);
x_302 = lean_box(0);
x_303 = l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(x_301, x_302, x_5, x_6, x_7, x_8, x_300);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l_Lean_Core_instantiateValueLevelParams(x_299, x_304, x_7, x_8, x_305);
lean_dec(x_299);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_box(0);
lean_inc(x_5);
x_310 = l_Lean_Meta_lambdaMetaTelescope(x_307, x_309, x_5, x_6, x_7, x_8, x_308);
lean_dec(x_307);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_ctor_get(x_312, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_317 = x_312;
} else {
 lean_dec_ref(x_312);
 x_317 = lean_box(0);
}
x_318 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_316);
if (lean_obj_tag(x_318) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_272);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = x_313;
goto block_42;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_357; uint8_t x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; lean_object* x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_405; uint8_t x_406; uint64_t x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_319 = lean_ctor_get(x_5, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 0);
lean_inc(x_320);
lean_dec(x_318);
x_357 = lean_ctor_get_uint8(x_319, 0);
x_358 = lean_ctor_get_uint8(x_319, 1);
x_359 = lean_ctor_get_uint8(x_319, 2);
x_360 = lean_ctor_get_uint8(x_319, 3);
x_361 = lean_ctor_get_uint8(x_319, 4);
x_362 = lean_box(0);
x_363 = lean_ctor_get_uint8(x_319, 6);
x_364 = lean_ctor_get_uint8(x_319, 7);
x_365 = lean_ctor_get_uint8(x_319, 8);
x_366 = lean_ctor_get_uint8(x_319, 9);
x_367 = lean_ctor_get_uint8(x_319, 10);
x_368 = lean_ctor_get_uint8(x_319, 11);
x_369 = lean_ctor_get_uint8(x_319, 12);
x_370 = lean_ctor_get_uint8(x_319, 13);
x_371 = lean_ctor_get_uint8(x_319, 14);
x_372 = lean_ctor_get_uint8(x_319, 15);
x_373 = lean_ctor_get_uint8(x_319, 16);
x_374 = lean_ctor_get_uint8(x_319, 17);
lean_dec(x_319);
x_375 = lean_mk_string_unchecked("Meta", 4, 4);
x_376 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_377 = lean_mk_string_unchecked("hint", 4, 4);
x_405 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_405, 0, x_357);
lean_ctor_set_uint8(x_405, 1, x_358);
lean_ctor_set_uint8(x_405, 2, x_359);
lean_ctor_set_uint8(x_405, 3, x_360);
lean_ctor_set_uint8(x_405, 4, x_361);
x_406 = lean_unbox(x_362);
lean_ctor_set_uint8(x_405, 5, x_406);
lean_ctor_set_uint8(x_405, 6, x_363);
lean_ctor_set_uint8(x_405, 7, x_364);
lean_ctor_set_uint8(x_405, 8, x_365);
lean_ctor_set_uint8(x_405, 9, x_366);
lean_ctor_set_uint8(x_405, 10, x_367);
lean_ctor_set_uint8(x_405, 11, x_368);
lean_ctor_set_uint8(x_405, 12, x_369);
lean_ctor_set_uint8(x_405, 13, x_370);
lean_ctor_set_uint8(x_405, 14, x_371);
lean_ctor_set_uint8(x_405, 15, x_372);
lean_ctor_set_uint8(x_405, 16, x_373);
lean_ctor_set_uint8(x_405, 17, x_374);
x_407 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_405);
x_408 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_409 = lean_ctor_get(x_5, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_5, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_5, 3);
lean_inc(x_411);
x_412 = lean_ctor_get(x_5, 4);
lean_inc(x_412);
x_413 = lean_ctor_get(x_5, 5);
lean_inc(x_413);
x_414 = lean_ctor_get(x_5, 6);
lean_inc(x_414);
x_415 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_416 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_417 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_417, 0, x_405);
lean_ctor_set(x_417, 1, x_409);
lean_ctor_set(x_417, 2, x_410);
lean_ctor_set(x_417, 3, x_411);
lean_ctor_set(x_417, 4, x_412);
lean_ctor_set(x_417, 5, x_413);
lean_ctor_set(x_417, 6, x_414);
lean_ctor_set_uint64(x_417, sizeof(void*)*7, x_407);
lean_ctor_set_uint8(x_417, sizeof(void*)*7 + 8, x_408);
lean_ctor_set_uint8(x_417, sizeof(void*)*7 + 9, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*7 + 10, x_416);
x_418 = lean_ctor_get(x_320, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_420 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_419, x_2, x_417, x_6, x_7, x_8, x_313);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; uint8_t x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_unbox(x_421);
lean_dec(x_421);
if (x_422 == 0)
{
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_3);
x_378 = x_420;
goto block_404;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_ctor_get(x_418, 1);
lean_inc(x_424);
lean_dec(x_418);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_425 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_424, x_3, x_417, x_6, x_7, x_8, x_423);
lean_dec(x_417);
x_378 = x_425;
goto block_404;
}
}
else
{
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_3);
x_378 = x_420;
goto block_404;
}
block_356:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_320, 1);
lean_inc(x_327);
lean_dec(x_320);
x_328 = lean_box(0);
x_329 = lean_box(0);
if (lean_is_scalar(x_317)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_317;
}
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
x_331 = l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(x_327, x_330, x_322, x_323, x_324, x_325, x_326);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec(x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; size_t x_340; size_t x_341; lean_object* x_342; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_335 = x_331;
} else {
 lean_dec_ref(x_331);
 x_335 = lean_box(0);
}
x_336 = lean_unsigned_to_nat(0u);
x_337 = lean_array_get_size(x_315);
x_338 = l_Array_toSubarray___redArg(x_315, x_336, x_337);
if (lean_is_scalar(x_335)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_335;
}
lean_ctor_set(x_339, 0, x_328);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_array_size(x_314);
x_341 = lean_usize_of_nat(x_336);
x_342 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(x_314, x_340, x_341, x_339, x_322, x_323, x_324, x_325, x_334);
lean_dec(x_314);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec(x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec(x_342);
x_274 = x_321;
x_275 = x_345;
goto block_297;
}
else
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
lean_dec(x_342);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_unbox(x_347);
lean_dec(x_347);
x_274 = x_348;
x_275 = x_346;
goto block_297;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_342, 1);
lean_inc(x_350);
lean_dec(x_342);
x_24 = x_349;
x_25 = x_350;
goto block_28;
}
}
else
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_315);
lean_dec(x_314);
x_351 = lean_ctor_get(x_331, 1);
lean_inc(x_351);
lean_dec(x_331);
x_352 = lean_ctor_get(x_333, 0);
lean_inc(x_352);
lean_dec(x_333);
x_353 = lean_unbox(x_352);
lean_dec(x_352);
x_274 = x_353;
x_275 = x_351;
goto block_297;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
x_354 = lean_ctor_get(x_331, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_331, 1);
lean_inc(x_355);
lean_dec(x_331);
x_24 = x_354;
x_25 = x_355;
goto block_28;
}
}
block_404:
{
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_unbox(x_379);
if (x_380 == 0)
{
lean_object* x_381; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_320);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_272);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_381 = lean_ctor_get(x_378, 1);
lean_inc(x_381);
lean_dec(x_378);
x_39 = x_381;
goto block_42;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_382 = lean_ctor_get(x_378, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_383 = x_378;
} else {
 lean_dec_ref(x_378);
 x_383 = lean_box(0);
}
x_384 = l_Lean_Name_mkStr3(x_375, x_376, x_377);
lean_inc(x_384);
x_385 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_384, x_5, x_6, x_7, x_8, x_382);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_unbox(x_386);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; uint8_t x_389; 
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_1);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_389 = lean_unbox(x_379);
lean_dec(x_379);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_321 = x_389;
x_322 = x_5;
x_323 = x_6;
x_324 = x_7;
x_325 = x_8;
x_326 = x_388;
goto block_356;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_391 = x_385;
} else {
 lean_dec_ref(x_385);
 x_391 = lean_box(0);
}
x_392 = lean_mk_string_unchecked("", 0, 0);
x_393 = l_Lean_stringToMessageData(x_392);
lean_dec(x_392);
x_394 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_391)) {
 x_395 = lean_alloc_ctor(7, 2, 0);
} else {
 x_395 = x_391;
 lean_ctor_set_tag(x_395, 7);
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
x_397 = l_Lean_stringToMessageData(x_396);
lean_dec(x_396);
if (lean_is_scalar(x_383)) {
 x_398 = lean_alloc_ctor(7, 2, 0);
} else {
 x_398 = x_383;
 lean_ctor_set_tag(x_398, 7);
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_384, x_398, x_5, x_6, x_7, x_8, x_390);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = lean_unbox(x_379);
lean_dec(x_379);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_321 = x_401;
x_322 = x_5;
x_323 = x_6;
x_324 = x_7;
x_325 = x_8;
x_326 = x_400;
goto block_356;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; 
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_320);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_402 = lean_ctor_get(x_378, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_378, 1);
lean_inc(x_403);
lean_dec(x_378);
x_24 = x_402;
x_25 = x_403;
goto block_28;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = lean_ctor_get(x_306, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_306, 1);
lean_inc(x_427);
lean_dec(x_306);
x_24 = x_426;
x_25 = x_427;
goto block_28;
}
}
else
{
lean_object* x_428; lean_object* x_429; 
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_428 = lean_ctor_get(x_298, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_298, 1);
lean_inc(x_429);
lean_dec(x_298);
x_24 = x_428;
x_25 = x_429;
goto block_28;
}
block_297:
{
if (x_274 == 0)
{
lean_dec(x_272);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_29 = x_274;
x_30 = x_275;
goto block_38;
}
else
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; 
x_276 = lean_box(0);
x_277 = lean_unbox(x_276);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_278 = l_Lean_Meta_processPostponed(x_4, x_277, x_5, x_6, x_7, x_8, x_275);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; 
lean_dec(x_13);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_279);
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = l_Lean_Meta_SavedState_restore___redArg(x_11, x_6, x_8, x_281);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_11);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_284 = x_282;
} else {
 lean_dec_ref(x_282);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_276);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_11);
x_286 = lean_ctor_get(x_278, 1);
lean_inc(x_286);
lean_dec(x_278);
x_287 = l_Lean_Meta_getPostponed___redArg(x_6, x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_PersistentArray_append___redArg(x_272, x_288);
lean_dec(x_288);
x_291 = l_Lean_Meta_setPostponed(x_290, x_5, x_6, x_7, x_8, x_289);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_279);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_272);
lean_dec(x_7);
lean_dec(x_5);
x_295 = lean_ctor_get(x_278, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_278, 1);
lean_inc(x_296);
lean_dec(x_278);
x_24 = x_295;
x_25 = x_296;
goto block_28;
}
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_473; 
x_430 = lean_ctor_get(x_44, 0);
x_431 = lean_ctor_get(x_44, 2);
x_432 = lean_ctor_get(x_44, 3);
x_433 = lean_ctor_get(x_44, 4);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_44);
x_434 = lean_ctor_get(x_45, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_45, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_45, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_45, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_45, 5);
lean_inc(x_438);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 lean_ctor_release(x_45, 5);
 x_439 = x_45;
} else {
 lean_dec_ref(x_45);
 x_439 = lean_box(0);
}
x_440 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_440);
if (lean_is_scalar(x_439)) {
 x_442 = lean_alloc_ctor(0, 6, 0);
} else {
 x_442 = x_439;
}
lean_ctor_set(x_442, 0, x_434);
lean_ctor_set(x_442, 1, x_435);
lean_ctor_set(x_442, 2, x_436);
lean_ctor_set(x_442, 3, x_437);
lean_ctor_set(x_442, 4, x_441);
lean_ctor_set(x_442, 5, x_438);
x_443 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_443, 0, x_430);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set(x_443, 2, x_431);
lean_ctor_set(x_443, 3, x_432);
lean_ctor_set(x_443, 4, x_433);
x_444 = lean_st_ref_set(x_6, x_443, x_46);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_446 = l_Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_445);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
lean_inc(x_1);
x_473 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_5, x_6, x_7, x_8, x_448);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = l_Lean_ConstantInfo_levelParams(x_474);
x_477 = lean_box(0);
x_478 = l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(x_476, x_477, x_5, x_6, x_7, x_8, x_475);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_481 = l_Lean_Core_instantiateValueLevelParams(x_474, x_479, x_7, x_8, x_480);
lean_dec(x_474);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_box(0);
lean_inc(x_5);
x_485 = l_Lean_Meta_lambdaMetaTelescope(x_482, x_484, x_5, x_6, x_7, x_8, x_483);
lean_dec(x_482);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
lean_dec(x_485);
x_489 = lean_ctor_get(x_486, 0);
lean_inc(x_489);
lean_dec(x_486);
x_490 = lean_ctor_get(x_487, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_487, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_492 = x_487;
} else {
 lean_dec_ref(x_487);
 x_492 = lean_box(0);
}
x_493 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(x_491);
if (lean_obj_tag(x_493) == 0)
{
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_447);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = x_488;
goto block_42;
}
else
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_532; uint8_t x_533; uint8_t x_534; uint8_t x_535; uint8_t x_536; lean_object* x_537; uint8_t x_538; uint8_t x_539; uint8_t x_540; uint8_t x_541; uint8_t x_542; uint8_t x_543; uint8_t x_544; uint8_t x_545; uint8_t x_546; uint8_t x_547; uint8_t x_548; uint8_t x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_580; uint8_t x_581; uint64_t x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_494 = lean_ctor_get(x_5, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 0);
lean_inc(x_495);
lean_dec(x_493);
x_532 = lean_ctor_get_uint8(x_494, 0);
x_533 = lean_ctor_get_uint8(x_494, 1);
x_534 = lean_ctor_get_uint8(x_494, 2);
x_535 = lean_ctor_get_uint8(x_494, 3);
x_536 = lean_ctor_get_uint8(x_494, 4);
x_537 = lean_box(0);
x_538 = lean_ctor_get_uint8(x_494, 6);
x_539 = lean_ctor_get_uint8(x_494, 7);
x_540 = lean_ctor_get_uint8(x_494, 8);
x_541 = lean_ctor_get_uint8(x_494, 9);
x_542 = lean_ctor_get_uint8(x_494, 10);
x_543 = lean_ctor_get_uint8(x_494, 11);
x_544 = lean_ctor_get_uint8(x_494, 12);
x_545 = lean_ctor_get_uint8(x_494, 13);
x_546 = lean_ctor_get_uint8(x_494, 14);
x_547 = lean_ctor_get_uint8(x_494, 15);
x_548 = lean_ctor_get_uint8(x_494, 16);
x_549 = lean_ctor_get_uint8(x_494, 17);
lean_dec(x_494);
x_550 = lean_mk_string_unchecked("Meta", 4, 4);
x_551 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_552 = lean_mk_string_unchecked("hint", 4, 4);
x_580 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_580, 0, x_532);
lean_ctor_set_uint8(x_580, 1, x_533);
lean_ctor_set_uint8(x_580, 2, x_534);
lean_ctor_set_uint8(x_580, 3, x_535);
lean_ctor_set_uint8(x_580, 4, x_536);
x_581 = lean_unbox(x_537);
lean_ctor_set_uint8(x_580, 5, x_581);
lean_ctor_set_uint8(x_580, 6, x_538);
lean_ctor_set_uint8(x_580, 7, x_539);
lean_ctor_set_uint8(x_580, 8, x_540);
lean_ctor_set_uint8(x_580, 9, x_541);
lean_ctor_set_uint8(x_580, 10, x_542);
lean_ctor_set_uint8(x_580, 11, x_543);
lean_ctor_set_uint8(x_580, 12, x_544);
lean_ctor_set_uint8(x_580, 13, x_545);
lean_ctor_set_uint8(x_580, 14, x_546);
lean_ctor_set_uint8(x_580, 15, x_547);
lean_ctor_set_uint8(x_580, 16, x_548);
lean_ctor_set_uint8(x_580, 17, x_549);
x_582 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_580);
x_583 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_584 = lean_ctor_get(x_5, 1);
lean_inc(x_584);
x_585 = lean_ctor_get(x_5, 2);
lean_inc(x_585);
x_586 = lean_ctor_get(x_5, 3);
lean_inc(x_586);
x_587 = lean_ctor_get(x_5, 4);
lean_inc(x_587);
x_588 = lean_ctor_get(x_5, 5);
lean_inc(x_588);
x_589 = lean_ctor_get(x_5, 6);
lean_inc(x_589);
x_590 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_591 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_592 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_592, 0, x_580);
lean_ctor_set(x_592, 1, x_584);
lean_ctor_set(x_592, 2, x_585);
lean_ctor_set(x_592, 3, x_586);
lean_ctor_set(x_592, 4, x_587);
lean_ctor_set(x_592, 5, x_588);
lean_ctor_set(x_592, 6, x_589);
lean_ctor_set_uint64(x_592, sizeof(void*)*7, x_582);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 8, x_583);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 9, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 10, x_591);
x_593 = lean_ctor_get(x_495, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_595 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_594, x_2, x_592, x_6, x_7, x_8, x_488);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; uint8_t x_597; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_unbox(x_596);
lean_dec(x_596);
if (x_597 == 0)
{
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_3);
x_553 = x_595;
goto block_579;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_595, 1);
lean_inc(x_598);
lean_dec(x_595);
x_599 = lean_ctor_get(x_593, 1);
lean_inc(x_599);
lean_dec(x_593);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_600 = l_Lean_Meta_tryUnificationHints_isDefEqPattern(x_599, x_3, x_592, x_6, x_7, x_8, x_598);
lean_dec(x_592);
x_553 = x_600;
goto block_579;
}
}
else
{
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_3);
x_553 = x_595;
goto block_579;
}
block_531:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_502 = lean_ctor_get(x_495, 1);
lean_inc(x_502);
lean_dec(x_495);
x_503 = lean_box(0);
x_504 = lean_box(0);
if (lean_is_scalar(x_492)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_492;
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
x_506 = l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(x_502, x_505, x_497, x_498, x_499, x_500, x_501);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec(x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; size_t x_515; size_t x_516; lean_object* x_517; 
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_510 = x_506;
} else {
 lean_dec_ref(x_506);
 x_510 = lean_box(0);
}
x_511 = lean_unsigned_to_nat(0u);
x_512 = lean_array_get_size(x_490);
x_513 = l_Array_toSubarray___redArg(x_490, x_511, x_512);
if (lean_is_scalar(x_510)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_510;
}
lean_ctor_set(x_514, 0, x_503);
lean_ctor_set(x_514, 1, x_513);
x_515 = lean_array_size(x_489);
x_516 = lean_usize_of_nat(x_511);
x_517 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(x_489, x_515, x_516, x_514, x_497, x_498, x_499, x_500, x_509);
lean_dec(x_489);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec(x_518);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
lean_dec(x_517);
x_449 = x_496;
x_450 = x_520;
goto block_472;
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_521 = lean_ctor_get(x_517, 1);
lean_inc(x_521);
lean_dec(x_517);
x_522 = lean_ctor_get(x_519, 0);
lean_inc(x_522);
lean_dec(x_519);
x_523 = lean_unbox(x_522);
lean_dec(x_522);
x_449 = x_523;
x_450 = x_521;
goto block_472;
}
}
else
{
lean_object* x_524; lean_object* x_525; 
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
x_524 = lean_ctor_get(x_517, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_517, 1);
lean_inc(x_525);
lean_dec(x_517);
x_24 = x_524;
x_25 = x_525;
goto block_28;
}
}
else
{
lean_object* x_526; lean_object* x_527; uint8_t x_528; 
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_490);
lean_dec(x_489);
x_526 = lean_ctor_get(x_506, 1);
lean_inc(x_526);
lean_dec(x_506);
x_527 = lean_ctor_get(x_508, 0);
lean_inc(x_527);
lean_dec(x_508);
x_528 = lean_unbox(x_527);
lean_dec(x_527);
x_449 = x_528;
x_450 = x_526;
goto block_472;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
x_529 = lean_ctor_get(x_506, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_506, 1);
lean_inc(x_530);
lean_dec(x_506);
x_24 = x_529;
x_25 = x_530;
goto block_28;
}
}
block_579:
{
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; uint8_t x_555; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_unbox(x_554);
if (x_555 == 0)
{
lean_object* x_556; 
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_495);
lean_dec(x_492);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_447);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_556 = lean_ctor_get(x_553, 1);
lean_inc(x_556);
lean_dec(x_553);
x_39 = x_556;
goto block_42;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_557 = lean_ctor_get(x_553, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_558 = x_553;
} else {
 lean_dec_ref(x_553);
 x_558 = lean_box(0);
}
x_559 = l_Lean_Name_mkStr3(x_550, x_551, x_552);
lean_inc(x_559);
x_560 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_559, x_5, x_6, x_7, x_8, x_557);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_unbox(x_561);
lean_dec(x_561);
if (x_562 == 0)
{
lean_object* x_563; uint8_t x_564; 
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_1);
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
x_564 = lean_unbox(x_554);
lean_dec(x_554);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_496 = x_564;
x_497 = x_5;
x_498 = x_6;
x_499 = x_7;
x_500 = x_8;
x_501 = x_563;
goto block_531;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_565 = lean_ctor_get(x_560, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_566 = x_560;
} else {
 lean_dec_ref(x_560);
 x_566 = lean_box(0);
}
x_567 = lean_mk_string_unchecked("", 0, 0);
x_568 = l_Lean_stringToMessageData(x_567);
lean_dec(x_567);
x_569 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_566)) {
 x_570 = lean_alloc_ctor(7, 2, 0);
} else {
 x_570 = x_566;
 lean_ctor_set_tag(x_570, 7);
}
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_mk_string_unchecked(" succeeded, applying constraints", 32, 32);
x_572 = l_Lean_stringToMessageData(x_571);
lean_dec(x_571);
if (lean_is_scalar(x_558)) {
 x_573 = lean_alloc_ctor(7, 2, 0);
} else {
 x_573 = x_558;
 lean_ctor_set_tag(x_573, 7);
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_572);
x_574 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_559, x_573, x_5, x_6, x_7, x_8, x_565);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
lean_dec(x_574);
x_576 = lean_unbox(x_554);
lean_dec(x_554);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_496 = x_576;
x_497 = x_5;
x_498 = x_6;
x_499 = x_7;
x_500 = x_8;
x_501 = x_575;
goto block_531;
}
}
}
else
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_495);
lean_dec(x_492);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_577 = lean_ctor_get(x_553, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_553, 1);
lean_inc(x_578);
lean_dec(x_553);
x_24 = x_577;
x_25 = x_578;
goto block_28;
}
}
}
}
else
{
lean_object* x_601; lean_object* x_602; 
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_601 = lean_ctor_get(x_481, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_481, 1);
lean_inc(x_602);
lean_dec(x_481);
x_24 = x_601;
x_25 = x_602;
goto block_28;
}
}
else
{
lean_object* x_603; lean_object* x_604; 
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_603 = lean_ctor_get(x_473, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_473, 1);
lean_inc(x_604);
lean_dec(x_473);
x_24 = x_603;
x_25 = x_604;
goto block_28;
}
block_472:
{
if (x_449 == 0)
{
lean_dec(x_447);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_29 = x_449;
x_30 = x_450;
goto block_38;
}
else
{
lean_object* x_451; uint8_t x_452; lean_object* x_453; 
x_451 = lean_box(0);
x_452 = lean_unbox(x_451);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_453 = l_Lean_Meta_processPostponed(x_4, x_452, x_5, x_6, x_7, x_8, x_450);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; uint8_t x_455; 
lean_dec(x_13);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_unbox(x_454);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_454);
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
lean_dec(x_453);
x_457 = l_Lean_Meta_SavedState_restore___redArg(x_11, x_6, x_8, x_456);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_11);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_11);
x_461 = lean_ctor_get(x_453, 1);
lean_inc(x_461);
lean_dec(x_453);
x_462 = l_Lean_Meta_getPostponed___redArg(x_6, x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = l_Lean_PersistentArray_append___redArg(x_447, x_463);
lean_dec(x_463);
x_466 = l_Lean_Meta_setPostponed(x_465, x_5, x_6, x_7, x_8, x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_454);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_447);
lean_dec(x_7);
lean_dec(x_5);
x_470 = lean_ctor_get(x_453, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_453, 1);
lean_inc(x_471);
lean_dec(x_453);
x_24 = x_470;
x_25 = x_471;
goto block_28;
}
}
}
}
block_23:
{
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_17 = l_Lean_Meta_SavedState_restore___redArg(x_11, x_6, x_8, x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
block_28:
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
x_14 = x_25;
x_15 = x_24;
x_16 = x_27;
goto block_23;
}
else
{
x_14 = x_25;
x_15 = x_24;
x_16 = x_26;
goto block_23;
}
}
block_38:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_SavedState_restore___redArg(x_11, x_6, x_8, x_30);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(x_29);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
block_42:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_29 = x_41;
x_30 = x_39;
goto block_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_exceptBoolEmoji(lean_box(0), x_4);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked(" hint ", 6, 6);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofName(x_1);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked(" at ", 4, 4);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_ofExpr(x_2);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed), 9, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_12 = lean_mk_string_unchecked("hint", 4, 4);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed), 9, 4);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_unbox(x_14);
x_18 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_15, x_17, x_16, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_checkpointDefEq___at___Lean_Meta_tryUnificationHints_tryCandidate_spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_tryUnificationHints_tryCandidate___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Meta_tryUnificationHints_tryCandidate(x_1, x_2, x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_box(0);
x_21 = lean_unbox(x_18);
lean_dec(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_free_object(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_23;
x_12 = x_19;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(x_3);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_add(x_6, x_38);
x_6 = x_39;
x_7 = x_36;
x_12 = x_32;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(x_3);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_32);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
return x_16;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_16, 0);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryUnificationHints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_10 = lean_mk_string_unchecked("hint", 4, 4);
x_11 = l_Lean_Name_mkStr3(x_8, x_9, x_10);
lean_inc(x_11);
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_195; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Meta_instInhabitedUnificationHints;
x_195 = lean_unbox(x_14);
lean_dec(x_14);
if (x_195 == 0)
{
lean_free_object(x_12);
lean_dec(x_11);
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_15;
goto block_194;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
lean_inc(x_1);
x_198 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_197);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_198);
lean_ctor_set(x_12, 0, x_197);
x_199 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_12);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_2);
x_202 = l_Lean_MessageData_ofExpr(x_2);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_197);
x_205 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_204, x_3, x_4, x_5, x_6, x_15);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_206;
goto block_194;
}
block_194:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Meta_getConfig(x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, 5);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(x_24);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(x_24);
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
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_22, 1);
x_33 = lean_ctor_get(x_22, 0);
lean_dec(x_33);
x_34 = l_Lean_Expr_isMVar(x_1);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_free_object(x_22);
x_35 = lean_st_ref_get(x_20, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_unificationHintExtension;
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*3);
lean_dec(x_42);
x_44 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_45 = l_Lean_ScopedEnvExtension_getState___redArg(x_16, x_40, x_39, x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_44, sizeof(void*)*1);
x_48 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 8);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_17, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_17, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_17, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_17, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_17, 6);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 9);
x_56 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 10);
x_57 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_53);
lean_ctor_set(x_57, 6, x_54);
lean_ctor_set_uint64(x_57, sizeof(void*)*7, x_47);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 8, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 9, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 10, x_56);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_1);
x_58 = l_Lean_Meta_DiscrTree_getMatch(lean_box(0), x_45, x_1, x_57, x_18, x_19, x_20, x_38);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_box(0);
x_62 = lean_box(0);
lean_ctor_set(x_35, 1, x_62);
lean_ctor_set(x_35, 0, x_61);
x_63 = lean_array_size(x_59);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(x_1, x_2, x_24, x_59, x_63, x_65, x_35, x_17, x_18, x_19, x_20, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_box(x_34);
lean_ctor_set(x_66, 0, x_71);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_box(x_34);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
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
uint8_t x_85; 
lean_free_object(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_58);
if (x_85 == 0)
{
return x_58;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_58, 0);
x_87 = lean_ctor_get(x_58, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_58);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint64_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_unificationHintExtension;
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get_uint8(x_94, sizeof(void*)*3);
lean_dec(x_94);
x_96 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_97 = l_Lean_ScopedEnvExtension_getState___redArg(x_16, x_92, x_91, x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint64(x_96, sizeof(void*)*1);
x_100 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 8);
x_101 = lean_ctor_get(x_17, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_17, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_17, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_17, 4);
lean_inc(x_104);
x_105 = lean_ctor_get(x_17, 5);
lean_inc(x_105);
x_106 = lean_ctor_get(x_17, 6);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 9);
x_108 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 10);
x_109 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_104);
lean_ctor_set(x_109, 5, x_105);
lean_ctor_set(x_109, 6, x_106);
lean_ctor_set_uint64(x_109, sizeof(void*)*7, x_99);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 8, x_100);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 9, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 10, x_108);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_1);
x_110 = l_Lean_Meta_DiscrTree_getMatch(lean_box(0), x_97, x_1, x_109, x_18, x_19, x_20, x_90);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; size_t x_118; lean_object* x_119; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_box(0);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_size(x_111);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_usize_of_nat(x_117);
x_119 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(x_1, x_2, x_24, x_111, x_116, x_118, x_115, x_17, x_18, x_19, x_20, x_112);
lean_dec(x_111);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
 x_123 = lean_box(0);
}
x_124 = lean_box(x_34);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
lean_dec(x_121);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_119, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_132 = x_119;
} else {
 lean_dec_ref(x_119);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_110, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_110, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_136 = x_110;
} else {
 lean_dec_ref(x_110);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_box(0);
lean_ctor_set(x_22, 0, x_138);
return x_22;
}
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_22, 1);
lean_inc(x_139);
lean_dec(x_22);
x_140 = l_Lean_Expr_isMVar(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint64_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_141 = lean_st_ref_get(x_20, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec(x_142);
x_146 = l_Lean_Meta_unificationHintExtension;
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_ctor_get_uint8(x_148, sizeof(void*)*3);
lean_dec(x_148);
x_150 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_151 = l_Lean_ScopedEnvExtension_getState___redArg(x_16, x_146, x_145, x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get_uint64(x_150, sizeof(void*)*1);
x_154 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 8);
x_155 = lean_ctor_get(x_17, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_17, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_17, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_17, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_17, 5);
lean_inc(x_159);
x_160 = lean_ctor_get(x_17, 6);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 9);
x_162 = lean_ctor_get_uint8(x_17, sizeof(void*)*7 + 10);
x_163 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
lean_ctor_set(x_163, 4, x_158);
lean_ctor_set(x_163, 5, x_159);
lean_ctor_set(x_163, 6, x_160);
lean_ctor_set_uint64(x_163, sizeof(void*)*7, x_153);
lean_ctor_set_uint8(x_163, sizeof(void*)*7 + 8, x_154);
lean_ctor_set_uint8(x_163, sizeof(void*)*7 + 9, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*7 + 10, x_162);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_1);
x_164 = l_Lean_Meta_DiscrTree_getMatch(lean_box(0), x_151, x_1, x_163, x_18, x_19, x_20, x_143);
lean_dec(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; size_t x_170; lean_object* x_171; size_t x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_box(0);
x_168 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_144;
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_size(x_165);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_usize_of_nat(x_171);
x_173 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(x_1, x_2, x_24, x_165, x_170, x_172, x_169, x_17, x_18, x_19, x_20, x_166);
lean_dec(x_165);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
x_178 = lean_box(x_140);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_181 = x_173;
} else {
 lean_dec_ref(x_173);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
lean_dec(x_175);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_173, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_173, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_186 = x_173;
} else {
 lean_dec_ref(x_173);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_164, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_164, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_190 = x_164;
} else {
 lean_dec_ref(x_164);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_139);
return x_193;
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_279; 
x_207 = lean_ctor_get(x_12, 0);
x_208 = lean_ctor_get(x_12, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_12);
x_209 = l_Lean_Meta_instInhabitedUnificationHints;
x_279 = lean_unbox(x_207);
lean_dec(x_207);
if (x_279 == 0)
{
lean_dec(x_11);
x_210 = x_3;
x_211 = x_4;
x_212 = x_5;
x_213 = x_6;
x_214 = x_208;
goto block_278;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_280 = lean_mk_string_unchecked("", 0, 0);
x_281 = l_Lean_stringToMessageData(x_280);
lean_dec(x_280);
lean_inc(x_1);
x_282 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_285 = l_Lean_stringToMessageData(x_284);
lean_dec(x_284);
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_285);
lean_inc(x_2);
x_287 = l_Lean_MessageData_ofExpr(x_2);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_281);
x_290 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_289, x_3, x_4, x_5, x_6, x_208);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_210 = x_3;
x_211 = x_4;
x_212 = x_5;
x_213 = x_6;
x_214 = x_291;
goto block_278;
}
block_278:
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = l_Lean_Meta_getConfig(x_210, x_211, x_212, x_213, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_216, 5);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_219 = x_215;
} else {
 lean_dec_ref(x_215);
 x_219 = lean_box(0);
}
x_220 = lean_box(x_217);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_215, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_223 = x_215;
} else {
 lean_dec_ref(x_215);
 x_223 = lean_box(0);
}
x_224 = l_Lean_Expr_isMVar(x_1);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint64_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_223);
x_225 = lean_st_ref_get(x_213, x_222);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
lean_dec(x_226);
x_230 = l_Lean_Meta_unificationHintExtension;
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get_uint8(x_232, sizeof(void*)*3);
lean_dec(x_232);
x_234 = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
x_235 = l_Lean_ScopedEnvExtension_getState___redArg(x_209, x_230, x_229, x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get_uint64(x_234, sizeof(void*)*1);
x_238 = lean_ctor_get_uint8(x_210, sizeof(void*)*7 + 8);
x_239 = lean_ctor_get(x_210, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_210, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_210, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_210, 4);
lean_inc(x_242);
x_243 = lean_ctor_get(x_210, 5);
lean_inc(x_243);
x_244 = lean_ctor_get(x_210, 6);
lean_inc(x_244);
x_245 = lean_ctor_get_uint8(x_210, sizeof(void*)*7 + 9);
x_246 = lean_ctor_get_uint8(x_210, sizeof(void*)*7 + 10);
x_247 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_247, 0, x_236);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set(x_247, 4, x_242);
lean_ctor_set(x_247, 5, x_243);
lean_ctor_set(x_247, 6, x_244);
lean_ctor_set_uint64(x_247, sizeof(void*)*7, x_237);
lean_ctor_set_uint8(x_247, sizeof(void*)*7 + 8, x_238);
lean_ctor_set_uint8(x_247, sizeof(void*)*7 + 9, x_245);
lean_ctor_set_uint8(x_247, sizeof(void*)*7 + 10, x_246);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_1);
x_248 = l_Lean_Meta_DiscrTree_getMatch(lean_box(0), x_235, x_1, x_247, x_211, x_212, x_213, x_227);
lean_dec(x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; size_t x_254; lean_object* x_255; size_t x_256; lean_object* x_257; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_box(0);
x_252 = lean_box(0);
if (lean_is_scalar(x_228)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_228;
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_array_size(x_249);
x_255 = lean_unsigned_to_nat(0u);
x_256 = lean_usize_of_nat(x_255);
x_257 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(x_1, x_2, x_217, x_249, x_254, x_256, x_253, x_210, x_211, x_212, x_213, x_250);
lean_dec(x_249);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec(x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_261 = x_257;
} else {
 lean_dec_ref(x_257);
 x_261 = lean_box(0);
}
x_262 = lean_box(x_224);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_257, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_265 = x_257;
} else {
 lean_dec_ref(x_257);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
lean_dec(x_259);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_257, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_257, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_270 = x_257;
} else {
 lean_dec_ref(x_257);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_228);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_2);
lean_dec(x_1);
x_272 = lean_ctor_get(x_248, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_248, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_274 = x_248;
} else {
 lean_dec_ref(x_248);
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
lean_object* x_276; lean_object* x_277; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_2);
lean_dec(x_1);
x_276 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_223;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_222);
return x_277;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_tryUnificationHints_spec__0(x_1, x_2, x_13, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2243_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("isDefEq", 7, 7);
x_4 = lean_mk_string_unchecked("hint", 4, 4);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_str___override(x_9, x_2);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_8);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = lean_mk_string_unchecked("UnificationHint", 15, 15);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(2243u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_unbox(x_6);
x_24 = l_Lean_registerTraceClass(x_5, x_23, x_22, x_1);
return x_24;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_UnificationHint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedUnificationHintEntry = _init_l_Lean_Meta_instInhabitedUnificationHintEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHintEntry);
l_Lean_Meta_instInhabitedUnificationHints = _init_l_Lean_Meta_instInhabitedUnificationHints();
lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints);
l_Lean_Meta_instToFormatUnificationHints = _init_l_Lean_Meta_instToFormatUnificationHints();
lean_mark_persistent(l_Lean_Meta_instToFormatUnificationHints);
l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config = _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config();
lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_112_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_unificationHintExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_unificationHintExtension);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_809_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_UnificationHint___hyg_2243_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
