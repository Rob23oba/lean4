// Lean compiler output
// Module: Lean.Message
// Imports: Lean.Data.Position Lean.Data.OpenDecl Lean.MetavarContext Lean.Environment Lean.Util.PPExt Lean.Util.Sorry
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
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr;
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeList;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object*);
extern lean_object* l_Std_instInhabitedFormat;
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object*);
lean_object* l_List_mapTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
extern lean_object* l_Lean_instFromJsonString;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164____boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeFormat;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage;
LEAN_EXPORT lean_object* l_String_split___at___Lean_stringToMessageData_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSyntax;
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr;
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString;
lean_object* l_Lean_instFromJsonOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeSyntax;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage___boxed(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr;
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataExpr;
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_formatRawGoal(lean_object*);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeLevel;
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_stringToMessageData_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataFormat;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___lam__0(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity;
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instTypeNameMessageData;
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_MessageData_orList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataString;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object*, lean_object*);
lean_object* l_Lean_ppConstNameWithInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_formatAux___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage;
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_empty;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_formatAux___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataLevel;
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn____x40_Lean_Message___hyg_1428_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity____x40_Lean_Message___hyg_164_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataMVarId;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object*, lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_MessageData_formatAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBTree_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonBaseMessage___redArg____x40_Lean_Message___hyg_2974_(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofName___lam__0(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125____boxed(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_termM_x21__;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lean_stringToMessageData_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonBaseMessage____x40_Lean_Message___hyg_2974_(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonBaseMessage___redArg____x40_Lean_Message___hyg_3128_(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_instAppend;
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataMessageData;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instImpl____x40_Lean_Message___hyg_606_;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_maxTraceChildren;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3128_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonSerialMessage____x40_Lean_Message___hyg_3511_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataName;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeExpr;
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeName;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString;
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg(uint8_t, uint8_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_stringToMessageData___boxed(lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_20; 
x_20 = lean_mk_string_unchecked("", 0, 0);
x_5 = x_20;
goto block_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_mk_string_unchecked("-", 1, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_5 = x_30;
goto block_19;
}
block_19:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked(":", 1, 1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_6);
lean_dec(x_6);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_5);
lean_dec(x_5);
x_16 = lean_mk_string_unchecked(": ", 2, 2);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_MessageSeverity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_MessageSeverity_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageSeverity_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_MessageSeverity_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_MessageSeverity_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_MessageSeverity_toCtorIdx(x_1);
x_4 = l_Lean_MessageSeverity_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqMessageSeverity() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("information", 11, 11);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("warning", 7, 7);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("error", 5, 5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonMessageSeverity() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("warning", 7, 7);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(1);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("information", 11, 11);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity____x40_Lean_Message___hyg_164_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("error", 5, 5);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164____boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
lean_inc(x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164____boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_6);
lean_dec(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Except_orElseLazy___redArg(x_9, x_8);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Except_orElseLazy___redArg(x_13, x_8);
lean_dec(x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_box(2);
lean_ctor_set(x_9, 0, x_17);
x_18 = l_Except_orElseLazy___redArg(x_9, x_8);
lean_dec(x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = lean_box(2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Except_orElseLazy___redArg(x_20, x_8);
lean_dec(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__0____x40_Lean_Message___hyg_164_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__1____x40_Lean_Message___hyg_164_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Message_0__Lean_fromJsonMessageSeverity___lam__2____x40_Lean_Message___hyg_164_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instFromJsonMessageSeverity() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonMessageSeverity____x40_Lean_Message___hyg_164_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instImpl____x40_Lean_Message___hyg_606_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("MessageData", 11, 11);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instTypeNameMessageData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_mk_string_unchecked("(invalid MessageData.lazy, missing context)", 43, 43);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_5 = x_12;
x_6 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_apply_2(x_2, x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_5 = x_15;
x_6 = x_16;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_MessageData_hasTag(x_1, x_6);
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
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_2 = x_3;
goto _start;
}
case 4:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
case 7:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_MessageData_hasTag(x_1, x_11);
if (x_13 == 0)
{
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_1);
return x_13;
}
}
case 8:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
x_2 = x_16;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_1);
return x_18;
}
}
case 9:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec(x_2);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
lean_inc(x_1);
x_32 = lean_apply_1(x_1, x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc(x_1);
x_34 = l_Lean_MessageData_hasTag(x_1, x_21);
x_23 = x_34;
goto block_30;
}
else
{
lean_dec(x_21);
x_23 = x_33;
goto block_30;
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_22);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_1);
return x_23;
}
else
{
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_1);
return x_23;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_usize_of_nat(x_24);
x_28 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_29 = l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0(x_1, x_22, x_27, x_28);
lean_dec(x_22);
return x_29;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_1);
return x_23;
}
}
}
default: 
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MessageData_hasTag_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_hasTag(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
case 4:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_kind(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_nil() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_mkPPContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Syntax_formatStx(x_2, x_13, x_15);
x_7 = x_16;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Lean_Syntax_copyHeadTailInfoFrom(x_3, x_4);
x_19 = l_Lean_ppTerm(x_17, x_18, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_7 = x_20;
x_8 = x_21;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_MessageData_ofFormat(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__0___boxed), 1, 0);
x_3 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = l_Lean_Syntax_copyHeadTailInfoFrom(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 6, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofSyntax___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MessageData_ofSyntax___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_instantiateMVarsCore(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Expr_hasSyntheticSorry(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_expr_dbg_to_string(x_2);
lean_dec(x_2);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_5 = x_14;
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_ppExprWithInfos(x_15, x_2, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofExpr___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Level_format(x_2, x_12);
x_5 = x_13;
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_ppLevel(x_14, x_2, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_5 = x_16;
x_6 = x_17;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MessageData_ofFormat(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__0___boxed), 1, 0);
x_3 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__1), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofName___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Name_toString(x_1, x_4, x_2);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofName___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Name_toString(x_2, x_18, x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_7 = x_22;
x_8 = x_6;
goto block_12;
}
else
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = l_Lean_ppConstNameWithInfos(x_23, x_2, x_6);
x_13 = x_24;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 3);
lean_inc(x_29);
x_30 = lean_mk_string_unchecked("pp", 2, 2);
x_31 = lean_mk_string_unchecked("fullNames", 9, 9);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_33, 0, x_4);
x_34 = l_Lean_KVMap_insert(x_29, x_32, x_33);
x_35 = lean_ctor_get(x_25, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_25, 5);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_36);
x_38 = l_Lean_ppConstNameWithInfos(x_37, x_2, x_6);
x_13 = x_38;
goto block_16;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_7 = x_14;
x_8 = x_15;
goto block_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__0___boxed), 1, 0);
x_5 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
x_6 = lean_box(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__2___boxed), 6, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_MessageData_ofConstName___lam__2(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_MessageData_ofConstName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_6);
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
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
case 4:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_2 = x_8;
goto _start;
}
case 5:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
case 6:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
case 7:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_14);
if (x_16 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_1);
return x_16;
}
}
case 8:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_2 = x_18;
goto _start;
}
case 9:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_1);
x_22 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_1);
return x_22;
}
else
{
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_1);
return x_22;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_usize_of_nat(x_23);
x_27 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_28 = l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0(x_1, x_21, x_26, x_27);
lean_dec(x_21);
return x_28;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_1);
return x_22;
}
}
case 10:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_31);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
lean_inc(x_31);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_ctor_set(x_38, 8, x_37);
x_39 = lean_apply_1(x_29, x_38);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_apply_1(x_41, x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
return x_44;
}
}
default: 
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MessageData_hasSyntheticSorry_visit_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn____x40_Lean_Message___hyg_1428_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("maxTraceChildren", 16, 16);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(50u);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("Maximum number of trace node children to display", 48, 48);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("MessageData", 11, 11);
x_10 = l_Lean_Name_mkStr3(x_8, x_9, x_2);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_3, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_4, x_3, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_13, x_3, x_10);
x_3 = x_16;
x_4 = x_17;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_MessageData_formatAux_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_instMonadEIO(lean_box(0));
x_4 = l_Std_instInhabitedFormat;
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_formatAux___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_formatAux___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_52; lean_object* x_53; lean_object* x_54; double x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_150; lean_object* x_151; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_alloc_closure((void*)(l_Lean_MessageData_formatAux___lam__0___boxed), 1, 0);
x_203 = l_Lean_instImpl____x40_Lean_Message___hyg_606_;
if (lean_obj_tag(x_2) == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_228; 
lean_dec(x_202);
lean_dec(x_1);
x_228 = lean_ctor_get(x_3, 0);
lean_inc(x_228);
lean_dec(x_3);
x_150 = x_228;
x_151 = x_4;
goto block_154;
}
case 1:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_202);
lean_dec(x_1);
x_229 = lean_ctor_get(x_3, 0);
lean_inc(x_229);
lean_dec(x_3);
x_230 = l_Lean_formatRawGoal(x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_4);
return x_231;
}
case 3:
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_202);
x_232 = lean_ctor_get(x_3, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_3, 1);
lean_inc(x_233);
lean_dec(x_3);
x_155 = x_1;
x_156 = x_232;
x_157 = x_233;
x_158 = x_4;
goto block_161;
}
case 4:
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_202);
lean_dec(x_1);
x_234 = lean_ctor_get(x_3, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_3, 1);
lean_inc(x_235);
lean_dec(x_3);
x_1 = x_234;
x_3 = x_235;
goto _start;
}
case 5:
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_202);
x_237 = lean_ctor_get(x_3, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_3, 1);
lean_inc(x_238);
lean_dec(x_3);
x_134 = x_1;
x_135 = x_2;
x_136 = x_237;
x_137 = x_238;
x_138 = x_4;
goto block_149;
}
case 6:
{
lean_object* x_239; 
lean_dec(x_202);
x_239 = lean_ctor_get(x_3, 0);
lean_inc(x_239);
lean_dec(x_3);
x_185 = x_1;
x_186 = x_2;
x_187 = x_239;
x_188 = x_4;
goto block_201;
}
case 7:
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_202);
x_240 = lean_ctor_get(x_3, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_3, 1);
lean_inc(x_241);
lean_dec(x_3);
x_162 = x_1;
x_163 = x_2;
x_164 = x_240;
x_165 = x_241;
x_166 = x_4;
goto block_184;
}
case 9:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_202);
x_242 = lean_ctor_get(x_3, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_3, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_3, 2);
lean_inc(x_244);
lean_dec(x_3);
x_74 = x_1;
x_75 = x_2;
x_76 = x_242;
x_77 = x_243;
x_78 = x_244;
x_79 = x_4;
goto block_133;
}
case 10:
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_3, 0);
lean_inc(x_245);
lean_dec(x_3);
x_246 = lean_box(0);
x_204 = x_2;
x_205 = x_1;
x_206 = x_4;
x_207 = x_245;
x_208 = x_246;
goto block_227;
}
default: 
{
lean_object* x_247; 
lean_dec(x_202);
x_247 = lean_ctor_get(x_3, 1);
lean_inc(x_247);
lean_dec(x_3);
x_3 = x_247;
goto _start;
}
}
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_249; 
lean_dec(x_202);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_3, 0);
lean_inc(x_249);
lean_dec(x_3);
x_150 = x_249;
x_151 = x_4;
goto block_154;
}
case 1:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_202);
x_250 = lean_ctor_get(x_2, 0);
lean_inc(x_250);
lean_dec(x_2);
x_251 = lean_ctor_get(x_3, 0);
lean_inc(x_251);
lean_dec(x_3);
x_252 = l_Lean_MessageData_mkPPContext(x_1, x_250);
lean_dec(x_250);
lean_dec(x_1);
x_253 = l_Lean_ppGoal(x_252, x_251, x_4);
return x_253;
}
case 3:
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_202);
lean_dec(x_2);
x_254 = lean_ctor_get(x_3, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_3, 1);
lean_inc(x_255);
lean_dec(x_3);
x_155 = x_1;
x_156 = x_254;
x_157 = x_255;
x_158 = x_4;
goto block_161;
}
case 4:
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_202);
lean_dec(x_1);
x_256 = lean_ctor_get(x_3, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_3, 1);
lean_inc(x_257);
lean_dec(x_3);
x_1 = x_256;
x_3 = x_257;
goto _start;
}
case 5:
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_202);
x_259 = lean_ctor_get(x_3, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_3, 1);
lean_inc(x_260);
lean_dec(x_3);
x_134 = x_1;
x_135 = x_2;
x_136 = x_259;
x_137 = x_260;
x_138 = x_4;
goto block_149;
}
case 6:
{
lean_object* x_261; 
lean_dec(x_202);
x_261 = lean_ctor_get(x_3, 0);
lean_inc(x_261);
lean_dec(x_3);
x_185 = x_1;
x_186 = x_2;
x_187 = x_261;
x_188 = x_4;
goto block_201;
}
case 7:
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_202);
x_262 = lean_ctor_get(x_3, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_3, 1);
lean_inc(x_263);
lean_dec(x_3);
x_162 = x_1;
x_163 = x_2;
x_164 = x_262;
x_165 = x_263;
x_166 = x_4;
goto block_184;
}
case 9:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_202);
x_264 = lean_ctor_get(x_3, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_3, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_3, 2);
lean_inc(x_266);
lean_dec(x_3);
x_74 = x_1;
x_75 = x_2;
x_76 = x_264;
x_77 = x_265;
x_78 = x_266;
x_79 = x_4;
goto block_133;
}
case 10:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_2, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_3, 0);
lean_inc(x_268);
lean_dec(x_3);
x_269 = l_Lean_MessageData_mkPPContext(x_1, x_267);
lean_dec(x_267);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_204 = x_2;
x_205 = x_1;
x_206 = x_4;
x_207 = x_268;
x_208 = x_270;
goto block_227;
}
default: 
{
lean_object* x_271; 
lean_dec(x_202);
x_271 = lean_ctor_get(x_3, 1);
lean_inc(x_271);
lean_dec(x_3);
x_3 = x_271;
goto _start;
}
}
}
block_51:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_MessageData_formatAux(x_6, x_5, x_8, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_15);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_mk_string_unchecked(" ", 1, 1);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_to_int(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_array_to_list(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("\n", 1, 1);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_26, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_mk_string_unchecked(" ", 1, 1);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_to_int(x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
x_44 = lean_array_to_list(x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("\n", 1, 1);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_45, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_32);
return x_50;
}
}
block_73:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; double x_67; double x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_mk_string_unchecked("", 0, 0);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
x_64 = lean_mk_string_unchecked(" [", 2, 2);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_ctor_get_float(x_56, sizeof(void*)*2 + 8);
lean_dec(x_56);
x_68 = lean_float_sub(x_67, x_55);
x_69 = lean_float_to_string(x_68);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_59);
x_5 = x_54;
x_6 = x_53;
x_7 = x_58;
x_8 = x_60;
x_9 = x_72;
x_10 = x_52;
goto block_51;
}
block_133:
{
lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
lean_inc(x_75);
lean_inc(x_74);
x_80 = lean_alloc_closure((void*)(l_Lean_MessageData_formatAux), 4, 2);
lean_closure_set(x_80, 0, x_74);
lean_closure_set(x_80, 1, x_75);
x_81 = lean_array_size(x_78);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_usize_of_nat(x_82);
x_84 = l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0(x_80, x_81, x_83, x_78, x_79);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_76, 0);
lean_inc(x_88);
x_89 = l_Lean_Name_isAnonymous(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; double x_102; double x_103; uint8_t x_104; 
lean_free_object(x_84);
x_90 = lean_box(x_89);
x_91 = lean_alloc_closure((void*)(l_Lean_MessageData_formatAux___lam__1___boxed), 2, 1);
lean_closure_set(x_91, 0, x_90);
x_92 = lean_mk_string_unchecked("[", 1, 1);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
x_96 = l_Lean_Name_toString(x_88, x_95, x_91);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("]", 1, 1);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_inc(x_100);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_ctor_get_float(x_76, sizeof(void*)*2);
x_103 = lean_float_of_nat(x_82);
x_104 = lean_float_beq(x_102, x_103);
if (x_104 == 0)
{
x_52 = x_87;
x_53 = x_74;
x_54 = x_75;
x_55 = x_102;
x_56 = x_76;
x_57 = x_101;
x_58 = x_86;
x_59 = x_100;
x_60 = x_77;
goto block_73;
}
else
{
if (x_89 == 0)
{
lean_dec(x_100);
lean_dec(x_76);
x_5 = x_75;
x_6 = x_74;
x_7 = x_86;
x_8 = x_77;
x_9 = x_101;
x_10 = x_87;
goto block_51;
}
else
{
x_52 = x_87;
x_53 = x_74;
x_54 = x_75;
x_55 = x_102;
x_56 = x_76;
x_57 = x_101;
x_58 = x_86;
x_59 = x_100;
x_60 = x_77;
goto block_73;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_105 = lean_array_to_list(x_86);
x_106 = lean_mk_string_unchecked("\n", 1, 1);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_105, x_107);
lean_ctor_set(x_84, 0, x_108);
return x_84;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_84, 0);
x_110 = lean_ctor_get(x_84, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_84);
x_111 = lean_ctor_get(x_76, 0);
lean_inc(x_111);
x_112 = l_Lean_Name_isAnonymous(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; double x_125; double x_126; uint8_t x_127; 
x_113 = lean_box(x_112);
x_114 = lean_alloc_closure((void*)(l_Lean_MessageData_formatAux___lam__1___boxed), 2, 1);
lean_closure_set(x_114, 0, x_113);
x_115 = lean_mk_string_unchecked("[", 1, 1);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_box(1);
x_118 = lean_unbox(x_117);
x_119 = l_Lean_Name_toString(x_111, x_118, x_114);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("]", 1, 1);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_inc(x_123);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_ctor_get_float(x_76, sizeof(void*)*2);
x_126 = lean_float_of_nat(x_82);
x_127 = lean_float_beq(x_125, x_126);
if (x_127 == 0)
{
x_52 = x_110;
x_53 = x_74;
x_54 = x_75;
x_55 = x_125;
x_56 = x_76;
x_57 = x_124;
x_58 = x_109;
x_59 = x_123;
x_60 = x_77;
goto block_73;
}
else
{
if (x_112 == 0)
{
lean_dec(x_123);
lean_dec(x_76);
x_5 = x_75;
x_6 = x_74;
x_7 = x_109;
x_8 = x_77;
x_9 = x_124;
x_10 = x_110;
goto block_51;
}
else
{
x_52 = x_110;
x_53 = x_74;
x_54 = x_75;
x_55 = x_125;
x_56 = x_76;
x_57 = x_124;
x_58 = x_109;
x_59 = x_123;
x_60 = x_77;
goto block_73;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_111);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_128 = lean_array_to_list(x_109);
x_129 = lean_mk_string_unchecked("\n", 1, 1);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_128, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_110);
return x_132;
}
}
}
block_149:
{
lean_object* x_139; uint8_t x_140; 
x_139 = l_Lean_MessageData_formatAux(x_134, x_135, x_137, x_138);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_nat_to_int(x_136);
x_143 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_139, 0);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_139);
x_146 = lean_nat_to_int(x_136);
x_147 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
block_154:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
block_161:
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_156);
x_1 = x_155;
x_2 = x_159;
x_3 = x_157;
x_4 = x_158;
goto _start;
}
block_184:
{
lean_object* x_167; uint8_t x_168; 
lean_inc(x_163);
lean_inc(x_162);
x_167 = l_Lean_MessageData_formatAux(x_162, x_163, x_164, x_166);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_167, 1);
x_170 = l_Lean_MessageData_formatAux(x_162, x_163, x_165, x_169);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
lean_ctor_set_tag(x_167, 5);
lean_ctor_set(x_167, 1, x_172);
lean_ctor_set(x_170, 0, x_167);
return x_170;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_170, 0);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_170);
lean_ctor_set_tag(x_167, 5);
lean_ctor_set(x_167, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_167, 0);
x_177 = lean_ctor_get(x_167, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_167);
x_178 = l_Lean_MessageData_formatAux(x_162, x_163, x_165, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_179);
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
block_201:
{
lean_object* x_189; uint8_t x_190; 
x_189 = l_Lean_MessageData_formatAux(x_185, x_186, x_187, x_188);
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_193, 0, x_191);
x_194 = lean_unbox(x_192);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_194);
lean_ctor_set(x_189, 0, x_193);
return x_189;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_189, 0);
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_189);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_198, 0, x_195);
x_199 = lean_unbox(x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_199);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_196);
return x_200;
}
}
block_227:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_apply_2(x_207, x_208, x_206);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_210, x_203);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_205);
lean_dec(x_204);
x_213 = lean_mk_string_unchecked("Lean.Message", 12, 12);
x_214 = lean_mk_string_unchecked("Lean.MessageData.formatAux", 26, 26);
x_215 = lean_unsigned_to_nat(265u);
x_216 = lean_unsigned_to_nat(8u);
x_217 = lean_mk_string_unchecked("MessageData.ofLazy: expected MessageData in Dynamic, got ", 57, 57);
x_218 = lean_ctor_get(x_210, 0);
lean_inc(x_218);
lean_dec(x_210);
x_219 = lean_box(1);
x_220 = lean_unbox(x_219);
x_221 = l_Lean_Name_toString(x_218, x_220, x_202);
x_222 = lean_string_append(x_217, x_221);
lean_dec(x_221);
x_223 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_213, x_214, x_215, x_216, x_222);
lean_dec(x_222);
lean_dec(x_214);
lean_dec(x_213);
x_224 = l_panic___at___Lean_MessageData_formatAux_spec__1(x_223, x_211);
return x_224;
}
else
{
lean_object* x_225; 
lean_dec(x_210);
lean_dec(x_202);
x_225 = lean_ctor_get(x_212, 0);
lean_inc(x_225);
lean_dec(x_212);
x_1 = x_205;
x_2 = x_204;
x_3 = x_225;
x_4 = x_211;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___Lean_MessageData_formatAux_spec__0(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_formatAux___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_MessageData_formatAux___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_MessageData_formatAux(x_6, x_2, x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_MessageData_format(x_1, x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(120u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_format_pretty(x_10, x_12, x_13, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instAppend___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeString___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormat), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_2);
lean_closure_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormat), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeName() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeSyntax() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeMVarId___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("none", 4, 4);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_MessageData_ofExpr(x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeOptionExpr___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("]", 1, 1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_mk_string_unchecked(", ", 2, 2);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofExpr(x_15);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_4 = x_23;
goto block_8;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_MessageData_ofExpr(x_15);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_4 = x_25;
goto block_8;
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_string_unchecked("#[", 2, 2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_MessageData_ofFormat(x_4);
x_6 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeArrayExpr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_MessageData_ofFormat(x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("(", 1, 1);
x_3 = lean_mk_string_unchecked(")", 1, 1);
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("[", 1, 1);
x_3 = lean_mk_string_unchecked("]", 1, 1);
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_2);
x_3 = lean_box(0);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
lean_inc(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_2);
lean_inc(x_5);
x_9 = l_Lean_MessageData_joinSep(x_5, x_2);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_inc(x_5);
x_16 = l_Lean_MessageData_joinSep(x_5, x_2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(7, 2, 0);
} else {
 x_18 = x_17;
 lean_ctor_set_tag(x_18, 7);
}
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_mk_string_unchecked(",", 1, 1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_box(1);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_MessageData_joinSep(x_1, x_10);
x_12 = l_Lean_MessageData_sbracket(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_MessageData_orList_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_mk_string_unchecked("'", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
lean_inc(x_17);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("– none –", 12, 8);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_mk_string_unchecked("'", 1, 1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
lean_inc(x_11);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("'", 1, 1);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_20 = lean_ctor_get(x_5, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = l_Lean_instInhabitedMessageData;
lean_inc(x_1);
x_23 = lean_array_mk(x_1);
x_24 = lean_array_pop(x_23);
x_25 = lean_array_to_list(x_24);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___Lean_MessageData_orList_spec__0(x_25, x_26);
x_28 = lean_mk_string_unchecked(", ", 2, 2);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = l_Lean_MessageData_joinSep(x_27, x_30);
x_32 = lean_mk_string_unchecked(" or '", 5, 5);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_34);
lean_ctor_set(x_5, 0, x_31);
x_35 = l_List_getLast_x21___redArg(x_22, x_1);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_1, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_5);
x_39 = lean_mk_string_unchecked("'", 1, 1);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_35);
x_44 = lean_mk_string_unchecked("'", 1, 1);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
x_48 = l_Lean_instInhabitedMessageData;
lean_inc(x_1);
x_49 = lean_array_mk(x_1);
x_50 = lean_array_pop(x_49);
x_51 = lean_array_to_list(x_50);
x_52 = lean_box(0);
x_53 = l_List_mapTR_loop___at___Lean_MessageData_orList_spec__0(x_51, x_52);
x_54 = lean_mk_string_unchecked(", ", 2, 2);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = l_Lean_MessageData_joinSep(x_53, x_56);
x_58 = lean_mk_string_unchecked(" or '", 5, 5);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_MessageData_ofFormat(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_List_getLast_x21___redArg(x_48, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_63 = x_1;
} else {
 lean_dec_ref(x_1);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_63;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_mk_string_unchecked("'", 1, 1);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("– none –", 12, 8);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_instInhabitedMessageData;
lean_inc(x_1);
x_11 = lean_array_mk(x_1);
x_12 = lean_array_pop(x_11);
x_13 = lean_array_to_list(x_12);
x_14 = lean_mk_string_unchecked(", ", 2, 2);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Lean_MessageData_joinSep(x_13, x_16);
x_18 = lean_mk_string_unchecked(" and ", 5, 5);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_17);
x_21 = l_List_getLast_x21___redArg(x_10, x_1);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_26 = l_Lean_instInhabitedMessageData;
lean_inc(x_1);
x_27 = lean_array_mk(x_1);
x_28 = lean_array_pop(x_27);
x_29 = lean_array_to_list(x_28);
x_30 = lean_mk_string_unchecked(", ", 2, 2);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = l_Lean_MessageData_joinSep(x_29, x_32);
x_34 = lean_mk_string_unchecked(" and ", 5, 5);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_getLast_x21___redArg(x_26, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(7, 2, 0);
} else {
 x_40 = x_39;
 lean_ctor_set_tag(x_40, 7);
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_instCoeList() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofList), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr), 1, 0);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_2, x_1, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeListExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeListExpr___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*5 + 1, x_10);
x_11 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*5 + 2, x_11);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedBaseMessage___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonBaseMessage___redArg____x40_Lean_Message___hyg_2974_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_58; 
x_3 = lean_mk_string_unchecked("fileName", 8, 8);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("pos", 3, 3);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_mk_string_unchecked("endPos", 6, 6);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_15 = x_59;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_60);
x_15 = x_61;
goto block_57;
}
block_57:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_mk_string_unchecked("keepFullRange", 13, 13);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_20 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
x_23 = lean_mk_string_unchecked("severity", 8, 8);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_25 = l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_mk_string_unchecked("isSilent", 8, 8);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
x_30 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
x_33 = lean_mk_string_unchecked("caption", 7, 7);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_mk_string_unchecked("data", 4, 4);
x_39 = lean_ctor_get(x_2, 4);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_apply_1(x_1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_13);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_52, 0, lean_box(0));
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = l_List_flatMapTR_go___redArg(x_52, x_51, x_54);
x_56 = l_Lean_Json_mkObj(x_55);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonBaseMessage____x40_Lean_Message___hyg_2974_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Message_0__Lean_toJsonBaseMessage___redArg____x40_Lean_Message___hyg_2974_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_toJsonBaseMessage____x40_Lean_Message___hyg_2974_), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_toJsonBaseMessage____x40_Lean_Message___hyg_2974_), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonBaseMessage___redArg____x40_Lean_Message___hyg_3128_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instFromJsonString;
x_4 = lean_mk_string_unchecked("fileName", 8, 8);
lean_inc(x_2);
x_5 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_inc(x_8);
x_14 = l_Lean_Name_toString(x_11, x_13, x_8);
x_15 = lean_mk_string_unchecked(".", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lean_Name_mkStr1(x_4);
x_18 = lean_unbox(x_12);
x_19 = l_Lean_Name_toString(x_17, x_18, x_8);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked(": ", 2, 2);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_25);
x_31 = l_Lean_Name_toString(x_28, x_30, x_25);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_4);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_25);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_24);
lean_dec(x_24);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_ctor_set_tag(x_5, 0);
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289_), 1, 0);
x_47 = lean_mk_string_unchecked("pos", 3, 3);
lean_inc(x_46);
lean_inc(x_2);
x_48 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_52 = lean_mk_string_unchecked("Lean", 4, 4);
x_53 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_51);
x_57 = l_Lean_Name_toString(x_54, x_56, x_51);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_47);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_51);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_50);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_66);
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
lean_dec(x_48);
x_68 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_71 = l_Lean_Name_mkStr2(x_69, x_70);
x_72 = lean_box(1);
x_73 = lean_unbox(x_72);
lean_inc(x_68);
x_74 = l_Lean_Name_toString(x_71, x_73, x_68);
x_75 = lean_mk_string_unchecked(".", 1, 1);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = l_Lean_Name_mkStr1(x_47);
x_78 = lean_unbox(x_72);
x_79 = l_Lean_Name_toString(x_77, x_78, x_68);
x_80 = lean_string_append(x_76, x_79);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked(": ", 2, 2);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = lean_string_append(x_82, x_67);
lean_dec(x_67);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_85; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_48);
if (x_85 == 0)
{
lean_ctor_set_tag(x_48, 0);
return x_48;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_48, 0);
lean_inc(x_86);
lean_dec(x_48);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_48, 0);
lean_inc(x_88);
lean_dec(x_48);
x_89 = lean_alloc_closure((void*)(l_Lean_instFromJsonOption___redArg___lam__0), 2, 1);
lean_closure_set(x_89, 0, x_46);
x_90 = lean_mk_string_unchecked("endPos", 6, 6);
lean_inc(x_2);
x_91 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_89, x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_95 = lean_mk_string_unchecked("Lean", 4, 4);
x_96 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_97 = l_Lean_Name_mkStr2(x_95, x_96);
x_98 = lean_box(1);
x_99 = lean_unbox(x_98);
lean_inc(x_94);
x_100 = l_Lean_Name_toString(x_97, x_99, x_94);
x_101 = lean_mk_string_unchecked(".", 1, 1);
x_102 = lean_string_append(x_100, x_101);
lean_dec(x_101);
x_103 = l_Lean_Name_mkStr1(x_90);
x_104 = lean_unbox(x_98);
x_105 = l_Lean_Name_toString(x_103, x_104, x_94);
x_106 = lean_string_append(x_102, x_105);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(": ", 2, 2);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_string_append(x_108, x_93);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_109);
return x_91;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_110 = lean_ctor_get(x_91, 0);
lean_inc(x_110);
lean_dec(x_91);
x_111 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_112 = lean_mk_string_unchecked("Lean", 4, 4);
x_113 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_114 = l_Lean_Name_mkStr2(x_112, x_113);
x_115 = lean_box(1);
x_116 = lean_unbox(x_115);
lean_inc(x_111);
x_117 = l_Lean_Name_toString(x_114, x_116, x_111);
x_118 = lean_mk_string_unchecked(".", 1, 1);
x_119 = lean_string_append(x_117, x_118);
lean_dec(x_118);
x_120 = l_Lean_Name_mkStr1(x_90);
x_121 = lean_unbox(x_115);
x_122 = l_Lean_Name_toString(x_120, x_121, x_111);
x_123 = lean_string_append(x_119, x_122);
lean_dec(x_122);
x_124 = lean_mk_string_unchecked(": ", 2, 2);
x_125 = lean_string_append(x_123, x_124);
lean_dec(x_124);
x_126 = lean_string_append(x_125, x_110);
lean_dec(x_110);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_128; 
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_91);
if (x_128 == 0)
{
lean_ctor_set_tag(x_91, 0);
return x_91;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_91, 0);
lean_inc(x_129);
lean_dec(x_91);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_91, 0);
lean_inc(x_131);
lean_dec(x_91);
x_132 = lean_alloc_closure((void*)(l_Lean_Json_getBool_x3f___boxed), 1, 0);
x_133 = lean_mk_string_unchecked("keepFullRange", 13, 13);
lean_inc(x_132);
lean_inc(x_2);
x_134 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_132, x_133);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_138 = lean_mk_string_unchecked("Lean", 4, 4);
x_139 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_140 = l_Lean_Name_mkStr2(x_138, x_139);
x_141 = lean_box(1);
x_142 = lean_unbox(x_141);
lean_inc(x_137);
x_143 = l_Lean_Name_toString(x_140, x_142, x_137);
x_144 = lean_mk_string_unchecked(".", 1, 1);
x_145 = lean_string_append(x_143, x_144);
lean_dec(x_144);
x_146 = l_Lean_Name_mkStr1(x_133);
x_147 = lean_unbox(x_141);
x_148 = l_Lean_Name_toString(x_146, x_147, x_137);
x_149 = lean_string_append(x_145, x_148);
lean_dec(x_148);
x_150 = lean_mk_string_unchecked(": ", 2, 2);
x_151 = lean_string_append(x_149, x_150);
lean_dec(x_150);
x_152 = lean_string_append(x_151, x_136);
lean_dec(x_136);
lean_ctor_set(x_134, 0, x_152);
return x_134;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
lean_dec(x_134);
x_154 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_155 = lean_mk_string_unchecked("Lean", 4, 4);
x_156 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_157 = l_Lean_Name_mkStr2(x_155, x_156);
x_158 = lean_box(1);
x_159 = lean_unbox(x_158);
lean_inc(x_154);
x_160 = l_Lean_Name_toString(x_157, x_159, x_154);
x_161 = lean_mk_string_unchecked(".", 1, 1);
x_162 = lean_string_append(x_160, x_161);
lean_dec(x_161);
x_163 = l_Lean_Name_mkStr1(x_133);
x_164 = lean_unbox(x_158);
x_165 = l_Lean_Name_toString(x_163, x_164, x_154);
x_166 = lean_string_append(x_162, x_165);
lean_dec(x_165);
x_167 = lean_mk_string_unchecked(": ", 2, 2);
x_168 = lean_string_append(x_166, x_167);
lean_dec(x_167);
x_169 = lean_string_append(x_168, x_153);
lean_dec(x_153);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
else
{
lean_dec(x_133);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_171; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_134);
if (x_171 == 0)
{
lean_ctor_set_tag(x_134, 0);
return x_134;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_134, 0);
lean_inc(x_172);
lean_dec(x_134);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_134, 0);
lean_inc(x_174);
lean_dec(x_134);
x_175 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonMessageSeverity____x40_Lean_Message___hyg_164_), 1, 0);
x_176 = lean_mk_string_unchecked("severity", 8, 8);
lean_inc(x_2);
x_177 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_175, x_176);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
lean_dec(x_174);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_181 = lean_mk_string_unchecked("Lean", 4, 4);
x_182 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_183 = l_Lean_Name_mkStr2(x_181, x_182);
x_184 = lean_box(1);
x_185 = lean_unbox(x_184);
lean_inc(x_180);
x_186 = l_Lean_Name_toString(x_183, x_185, x_180);
x_187 = lean_mk_string_unchecked(".", 1, 1);
x_188 = lean_string_append(x_186, x_187);
lean_dec(x_187);
x_189 = l_Lean_Name_mkStr1(x_176);
x_190 = lean_unbox(x_184);
x_191 = l_Lean_Name_toString(x_189, x_190, x_180);
x_192 = lean_string_append(x_188, x_191);
lean_dec(x_191);
x_193 = lean_mk_string_unchecked(": ", 2, 2);
x_194 = lean_string_append(x_192, x_193);
lean_dec(x_193);
x_195 = lean_string_append(x_194, x_179);
lean_dec(x_179);
lean_ctor_set(x_177, 0, x_195);
return x_177;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_196 = lean_ctor_get(x_177, 0);
lean_inc(x_196);
lean_dec(x_177);
x_197 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_198 = lean_mk_string_unchecked("Lean", 4, 4);
x_199 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_200 = l_Lean_Name_mkStr2(x_198, x_199);
x_201 = lean_box(1);
x_202 = lean_unbox(x_201);
lean_inc(x_197);
x_203 = l_Lean_Name_toString(x_200, x_202, x_197);
x_204 = lean_mk_string_unchecked(".", 1, 1);
x_205 = lean_string_append(x_203, x_204);
lean_dec(x_204);
x_206 = l_Lean_Name_mkStr1(x_176);
x_207 = lean_unbox(x_201);
x_208 = l_Lean_Name_toString(x_206, x_207, x_197);
x_209 = lean_string_append(x_205, x_208);
lean_dec(x_208);
x_210 = lean_mk_string_unchecked(": ", 2, 2);
x_211 = lean_string_append(x_209, x_210);
lean_dec(x_210);
x_212 = lean_string_append(x_211, x_196);
lean_dec(x_196);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
else
{
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_214; 
lean_dec(x_174);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_177);
if (x_214 == 0)
{
lean_ctor_set_tag(x_177, 0);
return x_177;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_177, 0);
lean_inc(x_215);
lean_dec(x_177);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_177, 0);
lean_inc(x_217);
lean_dec(x_177);
x_218 = lean_mk_string_unchecked("isSilent", 8, 8);
lean_inc(x_2);
x_219 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_132, x_218);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_223 = lean_mk_string_unchecked("Lean", 4, 4);
x_224 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_225 = l_Lean_Name_mkStr2(x_223, x_224);
x_226 = lean_box(1);
x_227 = lean_unbox(x_226);
lean_inc(x_222);
x_228 = l_Lean_Name_toString(x_225, x_227, x_222);
x_229 = lean_mk_string_unchecked(".", 1, 1);
x_230 = lean_string_append(x_228, x_229);
lean_dec(x_229);
x_231 = l_Lean_Name_mkStr1(x_218);
x_232 = lean_unbox(x_226);
x_233 = l_Lean_Name_toString(x_231, x_232, x_222);
x_234 = lean_string_append(x_230, x_233);
lean_dec(x_233);
x_235 = lean_mk_string_unchecked(": ", 2, 2);
x_236 = lean_string_append(x_234, x_235);
lean_dec(x_235);
x_237 = lean_string_append(x_236, x_221);
lean_dec(x_221);
lean_ctor_set(x_219, 0, x_237);
return x_219;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_238 = lean_ctor_get(x_219, 0);
lean_inc(x_238);
lean_dec(x_219);
x_239 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_240 = lean_mk_string_unchecked("Lean", 4, 4);
x_241 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_242 = l_Lean_Name_mkStr2(x_240, x_241);
x_243 = lean_box(1);
x_244 = lean_unbox(x_243);
lean_inc(x_239);
x_245 = l_Lean_Name_toString(x_242, x_244, x_239);
x_246 = lean_mk_string_unchecked(".", 1, 1);
x_247 = lean_string_append(x_245, x_246);
lean_dec(x_246);
x_248 = l_Lean_Name_mkStr1(x_218);
x_249 = lean_unbox(x_243);
x_250 = l_Lean_Name_toString(x_248, x_249, x_239);
x_251 = lean_string_append(x_247, x_250);
lean_dec(x_250);
x_252 = lean_mk_string_unchecked(": ", 2, 2);
x_253 = lean_string_append(x_251, x_252);
lean_dec(x_252);
x_254 = lean_string_append(x_253, x_238);
lean_dec(x_238);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
else
{
lean_dec(x_218);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_256; 
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_219);
if (x_256 == 0)
{
lean_ctor_set_tag(x_219, 0);
return x_219;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_219, 0);
lean_inc(x_257);
lean_dec(x_219);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_219, 0);
lean_inc(x_259);
lean_dec(x_219);
x_260 = lean_mk_string_unchecked("caption", 7, 7);
lean_inc(x_2);
x_261 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_3, x_260);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
lean_dec(x_259);
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_265 = lean_mk_string_unchecked("Lean", 4, 4);
x_266 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_267 = l_Lean_Name_mkStr2(x_265, x_266);
x_268 = lean_box(1);
x_269 = lean_unbox(x_268);
lean_inc(x_264);
x_270 = l_Lean_Name_toString(x_267, x_269, x_264);
x_271 = lean_mk_string_unchecked(".", 1, 1);
x_272 = lean_string_append(x_270, x_271);
lean_dec(x_271);
x_273 = l_Lean_Name_mkStr1(x_260);
x_274 = lean_unbox(x_268);
x_275 = l_Lean_Name_toString(x_273, x_274, x_264);
x_276 = lean_string_append(x_272, x_275);
lean_dec(x_275);
x_277 = lean_mk_string_unchecked(": ", 2, 2);
x_278 = lean_string_append(x_276, x_277);
lean_dec(x_277);
x_279 = lean_string_append(x_278, x_263);
lean_dec(x_263);
lean_ctor_set(x_261, 0, x_279);
return x_261;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_280 = lean_ctor_get(x_261, 0);
lean_inc(x_280);
lean_dec(x_261);
x_281 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_282 = lean_mk_string_unchecked("Lean", 4, 4);
x_283 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_284 = l_Lean_Name_mkStr2(x_282, x_283);
x_285 = lean_box(1);
x_286 = lean_unbox(x_285);
lean_inc(x_281);
x_287 = l_Lean_Name_toString(x_284, x_286, x_281);
x_288 = lean_mk_string_unchecked(".", 1, 1);
x_289 = lean_string_append(x_287, x_288);
lean_dec(x_288);
x_290 = l_Lean_Name_mkStr1(x_260);
x_291 = lean_unbox(x_285);
x_292 = l_Lean_Name_toString(x_290, x_291, x_281);
x_293 = lean_string_append(x_289, x_292);
lean_dec(x_292);
x_294 = lean_mk_string_unchecked(": ", 2, 2);
x_295 = lean_string_append(x_293, x_294);
lean_dec(x_294);
x_296 = lean_string_append(x_295, x_280);
lean_dec(x_280);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
else
{
lean_dec(x_260);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_298; 
lean_dec(x_259);
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_261);
if (x_298 == 0)
{
lean_ctor_set_tag(x_261, 0);
return x_261;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_261, 0);
lean_inc(x_299);
lean_dec(x_261);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_261, 0);
lean_inc(x_301);
lean_dec(x_261);
x_302 = lean_mk_string_unchecked("data", 4, 4);
x_303 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_1, x_302);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_304; 
lean_dec(x_301);
lean_dec(x_259);
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_305 = lean_ctor_get(x_303, 0);
x_306 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_307 = lean_mk_string_unchecked("Lean", 4, 4);
x_308 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_309 = l_Lean_Name_mkStr2(x_307, x_308);
x_310 = lean_box(1);
x_311 = lean_unbox(x_310);
lean_inc(x_306);
x_312 = l_Lean_Name_toString(x_309, x_311, x_306);
x_313 = lean_mk_string_unchecked(".", 1, 1);
x_314 = lean_string_append(x_312, x_313);
lean_dec(x_313);
x_315 = l_Lean_Name_mkStr1(x_302);
x_316 = lean_unbox(x_310);
x_317 = l_Lean_Name_toString(x_315, x_316, x_306);
x_318 = lean_string_append(x_314, x_317);
lean_dec(x_317);
x_319 = lean_mk_string_unchecked(": ", 2, 2);
x_320 = lean_string_append(x_318, x_319);
lean_dec(x_319);
x_321 = lean_string_append(x_320, x_305);
lean_dec(x_305);
lean_ctor_set(x_303, 0, x_321);
return x_303;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_322 = lean_ctor_get(x_303, 0);
lean_inc(x_322);
lean_dec(x_303);
x_323 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_324 = lean_mk_string_unchecked("Lean", 4, 4);
x_325 = lean_mk_string_unchecked("BaseMessage", 11, 11);
x_326 = l_Lean_Name_mkStr2(x_324, x_325);
x_327 = lean_box(1);
x_328 = lean_unbox(x_327);
lean_inc(x_323);
x_329 = l_Lean_Name_toString(x_326, x_328, x_323);
x_330 = lean_mk_string_unchecked(".", 1, 1);
x_331 = lean_string_append(x_329, x_330);
lean_dec(x_330);
x_332 = l_Lean_Name_mkStr1(x_302);
x_333 = lean_unbox(x_327);
x_334 = l_Lean_Name_toString(x_332, x_333, x_323);
x_335 = lean_string_append(x_331, x_334);
lean_dec(x_334);
x_336 = lean_mk_string_unchecked(": ", 2, 2);
x_337 = lean_string_append(x_335, x_336);
lean_dec(x_336);
x_338 = lean_string_append(x_337, x_322);
lean_dec(x_322);
x_339 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
}
else
{
lean_dec(x_302);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_340; 
lean_dec(x_301);
lean_dec(x_259);
lean_dec(x_217);
lean_dec(x_174);
lean_dec(x_131);
lean_dec(x_88);
lean_dec(x_45);
x_340 = !lean_is_exclusive(x_303);
if (x_340 == 0)
{
lean_ctor_set_tag(x_303, 0);
return x_303;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_303, 0);
lean_inc(x_341);
lean_dec(x_303);
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_341);
return x_342;
}
}
else
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_303);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_303, 0);
x_345 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_345, 0, x_45);
lean_ctor_set(x_345, 1, x_88);
lean_ctor_set(x_345, 2, x_131);
lean_ctor_set(x_345, 3, x_301);
lean_ctor_set(x_345, 4, x_344);
x_346 = lean_unbox(x_174);
lean_dec(x_174);
lean_ctor_set_uint8(x_345, sizeof(void*)*5, x_346);
x_347 = lean_unbox(x_217);
lean_dec(x_217);
lean_ctor_set_uint8(x_345, sizeof(void*)*5 + 1, x_347);
x_348 = lean_unbox(x_259);
lean_dec(x_259);
lean_ctor_set_uint8(x_345, sizeof(void*)*5 + 2, x_348);
lean_ctor_set(x_303, 0, x_345);
return x_303;
}
else
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; lean_object* x_354; 
x_349 = lean_ctor_get(x_303, 0);
lean_inc(x_349);
lean_dec(x_303);
x_350 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_350, 0, x_45);
lean_ctor_set(x_350, 1, x_88);
lean_ctor_set(x_350, 2, x_131);
lean_ctor_set(x_350, 3, x_301);
lean_ctor_set(x_350, 4, x_349);
x_351 = lean_unbox(x_174);
lean_dec(x_174);
lean_ctor_set_uint8(x_350, sizeof(void*)*5, x_351);
x_352 = lean_unbox(x_217);
lean_dec(x_217);
lean_ctor_set_uint8(x_350, sizeof(void*)*5 + 1, x_352);
x_353 = lean_unbox(x_259);
lean_dec(x_259);
lean_ctor_set_uint8(x_350, sizeof(void*)*5 + 2, x_353);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_350);
return x_354;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3128_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Message_0__Lean_fromJsonBaseMessage___redArg____x40_Lean_Message___hyg_3128_(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3128_), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3128_), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_toJsonSerialMessage____x40_Lean_Message___hyg_3511_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_67; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_3 = lean_mk_string_unchecked("fileName", 8, 8);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("pos", 3, 3);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_mk_string_unchecked("endPos", 6, 6);
x_67 = lean_ctor_get(x_4, 2);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_16 = x_68;
goto block_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_69);
x_16 = x_70;
goto block_66;
}
block_66:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_mk_string_unchecked("keepFullRange", 13, 13);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_21 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_mk_string_unchecked("severity", 8, 8);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_26 = l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_mk_string_unchecked("isSilent", 8, 8);
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 2);
x_31 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_mk_string_unchecked("caption", 7, 7);
x_35 = lean_ctor_get(x_4, 3);
lean_inc(x_35);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_mk_string_unchecked("data", 4, 4);
x_40 = lean_ctor_get(x_4, 4);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = lean_mk_string_unchecked("kind", 4, 4);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_Name_toString(x_45, x_47, x_2);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_18);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_9);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_mk_empty_array_with_capacity(x_62);
x_64 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_61, x_63);
x_65 = l_Lean_Json_mkObj(x_64);
return x_65;
}
}
}
static lean_object* _init_l_Lean_instToJsonSerialMessage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_toJsonSerialMessage____x40_Lean_Message___hyg_3511_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289_(x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Message_0__Lean_fromJsonMessageSeverity____x40_Lean_Message___hyg_164_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("fileName", 8, 8);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_6);
x_12 = l_Lean_Name_toString(x_9, x_11, x_6);
x_13 = lean_mk_string_unchecked(".", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_Name_mkStr1(x_2);
x_16 = lean_unbox(x_10);
x_17 = l_Lean_Name_toString(x_15, x_16, x_6);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked(": ", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_23);
x_29 = l_Lean_Name_toString(x_26, x_28, x_23);
x_30 = lean_mk_string_unchecked(".", 1, 1);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lean_Name_mkStr1(x_2);
x_33 = lean_unbox(x_27);
x_34 = l_Lean_Name_toString(x_32, x_33, x_23);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked(": ", 2, 2);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_22);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_mk_string_unchecked("pos", 3, 3);
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_48);
x_54 = l_Lean_Name_toString(x_51, x_53, x_48);
x_55 = lean_mk_string_unchecked(".", 1, 1);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = l_Lean_Name_mkStr1(x_44);
x_58 = lean_unbox(x_52);
x_59 = l_Lean_Name_toString(x_57, x_58, x_48);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked(": ", 2, 2);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
x_63 = lean_string_append(x_62, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_63);
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = lean_box(1);
x_70 = lean_unbox(x_69);
lean_inc(x_65);
x_71 = l_Lean_Name_toString(x_68, x_70, x_65);
x_72 = lean_mk_string_unchecked(".", 1, 1);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lean_Name_mkStr1(x_44);
x_75 = lean_unbox(x_69);
x_76 = l_Lean_Name_toString(x_74, x_75, x_65);
x_77 = lean_string_append(x_73, x_76);
lean_dec(x_76);
x_78 = lean_mk_string_unchecked(": ", 2, 2);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = lean_string_append(x_79, x_64);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_82; 
lean_dec(x_43);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_45);
if (x_82 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_45, 0);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_45, 0);
lean_inc(x_85);
lean_dec(x_45);
x_86 = lean_mk_string_unchecked("endPos", 6, 6);
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
lean_inc(x_90);
x_96 = l_Lean_Name_toString(x_93, x_95, x_90);
x_97 = lean_mk_string_unchecked(".", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = l_Lean_Name_mkStr1(x_86);
x_100 = lean_unbox(x_94);
x_101 = l_Lean_Name_toString(x_99, x_100, x_90);
x_102 = lean_string_append(x_98, x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked(": ", 2, 2);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_string_append(x_104, x_89);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_105);
return x_87;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec(x_87);
x_107 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_108 = lean_mk_string_unchecked("Lean", 4, 4);
x_109 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_110 = l_Lean_Name_mkStr2(x_108, x_109);
x_111 = lean_box(1);
x_112 = lean_unbox(x_111);
lean_inc(x_107);
x_113 = l_Lean_Name_toString(x_110, x_112, x_107);
x_114 = lean_mk_string_unchecked(".", 1, 1);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = l_Lean_Name_mkStr1(x_86);
x_117 = lean_unbox(x_111);
x_118 = l_Lean_Name_toString(x_116, x_117, x_107);
x_119 = lean_string_append(x_115, x_118);
lean_dec(x_118);
x_120 = lean_mk_string_unchecked(": ", 2, 2);
x_121 = lean_string_append(x_119, x_120);
lean_dec(x_120);
x_122 = lean_string_append(x_121, x_106);
lean_dec(x_106);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_124; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_87);
if (x_124 == 0)
{
lean_ctor_set_tag(x_87, 0);
return x_87;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_87, 0);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_87, 0);
lean_inc(x_127);
lean_dec(x_87);
x_128 = lean_mk_string_unchecked("keepFullRange", 13, 13);
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_133 = lean_mk_string_unchecked("Lean", 4, 4);
x_134 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_135 = l_Lean_Name_mkStr2(x_133, x_134);
x_136 = lean_box(1);
x_137 = lean_unbox(x_136);
lean_inc(x_132);
x_138 = l_Lean_Name_toString(x_135, x_137, x_132);
x_139 = lean_mk_string_unchecked(".", 1, 1);
x_140 = lean_string_append(x_138, x_139);
lean_dec(x_139);
x_141 = l_Lean_Name_mkStr1(x_128);
x_142 = lean_unbox(x_136);
x_143 = l_Lean_Name_toString(x_141, x_142, x_132);
x_144 = lean_string_append(x_140, x_143);
lean_dec(x_143);
x_145 = lean_mk_string_unchecked(": ", 2, 2);
x_146 = lean_string_append(x_144, x_145);
lean_dec(x_145);
x_147 = lean_string_append(x_146, x_131);
lean_dec(x_131);
lean_ctor_set(x_129, 0, x_147);
return x_129;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec(x_129);
x_149 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = lean_box(1);
x_154 = lean_unbox(x_153);
lean_inc(x_149);
x_155 = l_Lean_Name_toString(x_152, x_154, x_149);
x_156 = lean_mk_string_unchecked(".", 1, 1);
x_157 = lean_string_append(x_155, x_156);
lean_dec(x_156);
x_158 = l_Lean_Name_mkStr1(x_128);
x_159 = lean_unbox(x_153);
x_160 = l_Lean_Name_toString(x_158, x_159, x_149);
x_161 = lean_string_append(x_157, x_160);
lean_dec(x_160);
x_162 = lean_mk_string_unchecked(": ", 2, 2);
x_163 = lean_string_append(x_161, x_162);
lean_dec(x_162);
x_164 = lean_string_append(x_163, x_148);
lean_dec(x_148);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_129);
if (x_166 == 0)
{
lean_ctor_set_tag(x_129, 0);
return x_129;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_129, 0);
lean_inc(x_167);
lean_dec(x_129);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_129, 0);
lean_inc(x_169);
lean_dec(x_129);
x_170 = lean_mk_string_unchecked("severity", 8, 8);
lean_inc(x_1);
x_171 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3(x_1, x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_175 = lean_mk_string_unchecked("Lean", 4, 4);
x_176 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_177 = l_Lean_Name_mkStr2(x_175, x_176);
x_178 = lean_box(1);
x_179 = lean_unbox(x_178);
lean_inc(x_174);
x_180 = l_Lean_Name_toString(x_177, x_179, x_174);
x_181 = lean_mk_string_unchecked(".", 1, 1);
x_182 = lean_string_append(x_180, x_181);
lean_dec(x_181);
x_183 = l_Lean_Name_mkStr1(x_170);
x_184 = lean_unbox(x_178);
x_185 = l_Lean_Name_toString(x_183, x_184, x_174);
x_186 = lean_string_append(x_182, x_185);
lean_dec(x_185);
x_187 = lean_mk_string_unchecked(": ", 2, 2);
x_188 = lean_string_append(x_186, x_187);
lean_dec(x_187);
x_189 = lean_string_append(x_188, x_173);
lean_dec(x_173);
lean_ctor_set(x_171, 0, x_189);
return x_171;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
lean_dec(x_171);
x_191 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_192 = lean_mk_string_unchecked("Lean", 4, 4);
x_193 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_194 = l_Lean_Name_mkStr2(x_192, x_193);
x_195 = lean_box(1);
x_196 = lean_unbox(x_195);
lean_inc(x_191);
x_197 = l_Lean_Name_toString(x_194, x_196, x_191);
x_198 = lean_mk_string_unchecked(".", 1, 1);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = l_Lean_Name_mkStr1(x_170);
x_201 = lean_unbox(x_195);
x_202 = l_Lean_Name_toString(x_200, x_201, x_191);
x_203 = lean_string_append(x_199, x_202);
lean_dec(x_202);
x_204 = lean_mk_string_unchecked(": ", 2, 2);
x_205 = lean_string_append(x_203, x_204);
lean_dec(x_204);
x_206 = lean_string_append(x_205, x_190);
lean_dec(x_190);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
else
{
lean_dec(x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_208; 
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_171);
if (x_208 == 0)
{
lean_ctor_set_tag(x_171, 0);
return x_171;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_171, 0);
lean_inc(x_209);
lean_dec(x_171);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_171, 0);
lean_inc(x_211);
lean_dec(x_171);
x_212 = lean_mk_string_unchecked("isSilent", 8, 8);
lean_inc(x_1);
x_213 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_212);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_217 = lean_mk_string_unchecked("Lean", 4, 4);
x_218 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_219 = l_Lean_Name_mkStr2(x_217, x_218);
x_220 = lean_box(1);
x_221 = lean_unbox(x_220);
lean_inc(x_216);
x_222 = l_Lean_Name_toString(x_219, x_221, x_216);
x_223 = lean_mk_string_unchecked(".", 1, 1);
x_224 = lean_string_append(x_222, x_223);
lean_dec(x_223);
x_225 = l_Lean_Name_mkStr1(x_212);
x_226 = lean_unbox(x_220);
x_227 = l_Lean_Name_toString(x_225, x_226, x_216);
x_228 = lean_string_append(x_224, x_227);
lean_dec(x_227);
x_229 = lean_mk_string_unchecked(": ", 2, 2);
x_230 = lean_string_append(x_228, x_229);
lean_dec(x_229);
x_231 = lean_string_append(x_230, x_215);
lean_dec(x_215);
lean_ctor_set(x_213, 0, x_231);
return x_213;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_232 = lean_ctor_get(x_213, 0);
lean_inc(x_232);
lean_dec(x_213);
x_233 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_234 = lean_mk_string_unchecked("Lean", 4, 4);
x_235 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_236 = l_Lean_Name_mkStr2(x_234, x_235);
x_237 = lean_box(1);
x_238 = lean_unbox(x_237);
lean_inc(x_233);
x_239 = l_Lean_Name_toString(x_236, x_238, x_233);
x_240 = lean_mk_string_unchecked(".", 1, 1);
x_241 = lean_string_append(x_239, x_240);
lean_dec(x_240);
x_242 = l_Lean_Name_mkStr1(x_212);
x_243 = lean_unbox(x_237);
x_244 = l_Lean_Name_toString(x_242, x_243, x_233);
x_245 = lean_string_append(x_241, x_244);
lean_dec(x_244);
x_246 = lean_mk_string_unchecked(": ", 2, 2);
x_247 = lean_string_append(x_245, x_246);
lean_dec(x_246);
x_248 = lean_string_append(x_247, x_232);
lean_dec(x_232);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
else
{
lean_dec(x_212);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_250; 
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_213);
if (x_250 == 0)
{
lean_ctor_set_tag(x_213, 0);
return x_213;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_213, 0);
lean_inc(x_251);
lean_dec(x_213);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_213, 0);
lean_inc(x_253);
lean_dec(x_213);
x_254 = lean_mk_string_unchecked("caption", 7, 7);
lean_inc(x_1);
x_255 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(x_1, x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_259 = lean_mk_string_unchecked("Lean", 4, 4);
x_260 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_261 = l_Lean_Name_mkStr2(x_259, x_260);
x_262 = lean_box(1);
x_263 = lean_unbox(x_262);
lean_inc(x_258);
x_264 = l_Lean_Name_toString(x_261, x_263, x_258);
x_265 = lean_mk_string_unchecked(".", 1, 1);
x_266 = lean_string_append(x_264, x_265);
lean_dec(x_265);
x_267 = l_Lean_Name_mkStr1(x_254);
x_268 = lean_unbox(x_262);
x_269 = l_Lean_Name_toString(x_267, x_268, x_258);
x_270 = lean_string_append(x_266, x_269);
lean_dec(x_269);
x_271 = lean_mk_string_unchecked(": ", 2, 2);
x_272 = lean_string_append(x_270, x_271);
lean_dec(x_271);
x_273 = lean_string_append(x_272, x_257);
lean_dec(x_257);
lean_ctor_set(x_255, 0, x_273);
return x_255;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_274 = lean_ctor_get(x_255, 0);
lean_inc(x_274);
lean_dec(x_255);
x_275 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_276 = lean_mk_string_unchecked("Lean", 4, 4);
x_277 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_278 = l_Lean_Name_mkStr2(x_276, x_277);
x_279 = lean_box(1);
x_280 = lean_unbox(x_279);
lean_inc(x_275);
x_281 = l_Lean_Name_toString(x_278, x_280, x_275);
x_282 = lean_mk_string_unchecked(".", 1, 1);
x_283 = lean_string_append(x_281, x_282);
lean_dec(x_282);
x_284 = l_Lean_Name_mkStr1(x_254);
x_285 = lean_unbox(x_279);
x_286 = l_Lean_Name_toString(x_284, x_285, x_275);
x_287 = lean_string_append(x_283, x_286);
lean_dec(x_286);
x_288 = lean_mk_string_unchecked(": ", 2, 2);
x_289 = lean_string_append(x_287, x_288);
lean_dec(x_288);
x_290 = lean_string_append(x_289, x_274);
lean_dec(x_274);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
else
{
lean_dec(x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_292; 
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_255);
if (x_292 == 0)
{
lean_ctor_set_tag(x_255, 0);
return x_255;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_255, 0);
lean_inc(x_293);
lean_dec(x_255);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_255, 0);
lean_inc(x_295);
lean_dec(x_255);
x_296 = lean_mk_string_unchecked("data", 4, 4);
lean_inc(x_1);
x_297 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(x_1, x_296);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_298; 
lean_dec(x_295);
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_301 = lean_mk_string_unchecked("Lean", 4, 4);
x_302 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_303 = l_Lean_Name_mkStr2(x_301, x_302);
x_304 = lean_box(1);
x_305 = lean_unbox(x_304);
lean_inc(x_300);
x_306 = l_Lean_Name_toString(x_303, x_305, x_300);
x_307 = lean_mk_string_unchecked(".", 1, 1);
x_308 = lean_string_append(x_306, x_307);
lean_dec(x_307);
x_309 = l_Lean_Name_mkStr1(x_296);
x_310 = lean_unbox(x_304);
x_311 = l_Lean_Name_toString(x_309, x_310, x_300);
x_312 = lean_string_append(x_308, x_311);
lean_dec(x_311);
x_313 = lean_mk_string_unchecked(": ", 2, 2);
x_314 = lean_string_append(x_312, x_313);
lean_dec(x_313);
x_315 = lean_string_append(x_314, x_299);
lean_dec(x_299);
lean_ctor_set(x_297, 0, x_315);
return x_297;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_316 = lean_ctor_get(x_297, 0);
lean_inc(x_316);
lean_dec(x_297);
x_317 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_318 = lean_mk_string_unchecked("Lean", 4, 4);
x_319 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_320 = l_Lean_Name_mkStr2(x_318, x_319);
x_321 = lean_box(1);
x_322 = lean_unbox(x_321);
lean_inc(x_317);
x_323 = l_Lean_Name_toString(x_320, x_322, x_317);
x_324 = lean_mk_string_unchecked(".", 1, 1);
x_325 = lean_string_append(x_323, x_324);
lean_dec(x_324);
x_326 = l_Lean_Name_mkStr1(x_296);
x_327 = lean_unbox(x_321);
x_328 = l_Lean_Name_toString(x_326, x_327, x_317);
x_329 = lean_string_append(x_325, x_328);
lean_dec(x_328);
x_330 = lean_mk_string_unchecked(": ", 2, 2);
x_331 = lean_string_append(x_329, x_330);
lean_dec(x_330);
x_332 = lean_string_append(x_331, x_316);
lean_dec(x_316);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
}
else
{
lean_dec(x_296);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_334; 
lean_dec(x_295);
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_297);
if (x_334 == 0)
{
lean_ctor_set_tag(x_297, 0);
return x_297;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_297, 0);
lean_inc(x_335);
lean_dec(x_297);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_335);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_297, 0);
lean_inc(x_337);
lean_dec(x_297);
x_338 = lean_mk_string_unchecked("kind", 4, 4);
x_339 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(x_1, x_338);
if (lean_obj_tag(x_339) == 0)
{
uint8_t x_340; 
lean_dec(x_337);
lean_dec(x_295);
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_340 = !lean_is_exclusive(x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_341 = lean_ctor_get(x_339, 0);
x_342 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_343 = lean_mk_string_unchecked("Lean", 4, 4);
x_344 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_345 = l_Lean_Name_mkStr2(x_343, x_344);
x_346 = lean_box(1);
x_347 = lean_unbox(x_346);
lean_inc(x_342);
x_348 = l_Lean_Name_toString(x_345, x_347, x_342);
x_349 = lean_mk_string_unchecked(".", 1, 1);
x_350 = lean_string_append(x_348, x_349);
lean_dec(x_349);
x_351 = l_Lean_Name_mkStr1(x_338);
x_352 = lean_unbox(x_346);
x_353 = l_Lean_Name_toString(x_351, x_352, x_342);
x_354 = lean_string_append(x_350, x_353);
lean_dec(x_353);
x_355 = lean_mk_string_unchecked(": ", 2, 2);
x_356 = lean_string_append(x_354, x_355);
lean_dec(x_355);
x_357 = lean_string_append(x_356, x_341);
lean_dec(x_341);
lean_ctor_set(x_339, 0, x_357);
return x_339;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_358 = lean_ctor_get(x_339, 0);
lean_inc(x_358);
lean_dec(x_339);
x_359 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_360 = lean_mk_string_unchecked("Lean", 4, 4);
x_361 = lean_mk_string_unchecked("SerialMessage", 13, 13);
x_362 = l_Lean_Name_mkStr2(x_360, x_361);
x_363 = lean_box(1);
x_364 = lean_unbox(x_363);
lean_inc(x_359);
x_365 = l_Lean_Name_toString(x_362, x_364, x_359);
x_366 = lean_mk_string_unchecked(".", 1, 1);
x_367 = lean_string_append(x_365, x_366);
lean_dec(x_366);
x_368 = l_Lean_Name_mkStr1(x_338);
x_369 = lean_unbox(x_363);
x_370 = l_Lean_Name_toString(x_368, x_369, x_359);
x_371 = lean_string_append(x_367, x_370);
lean_dec(x_370);
x_372 = lean_mk_string_unchecked(": ", 2, 2);
x_373 = lean_string_append(x_371, x_372);
lean_dec(x_372);
x_374 = lean_string_append(x_373, x_358);
lean_dec(x_358);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_374);
return x_375;
}
}
else
{
lean_dec(x_338);
if (lean_obj_tag(x_339) == 0)
{
uint8_t x_376; 
lean_dec(x_337);
lean_dec(x_295);
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_376 = !lean_is_exclusive(x_339);
if (x_376 == 0)
{
lean_ctor_set_tag(x_339, 0);
return x_339;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_339, 0);
lean_inc(x_377);
lean_dec(x_339);
x_378 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_378, 0, x_377);
return x_378;
}
}
else
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_339);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_383; uint8_t x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_339, 0);
x_381 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_381, 0, x_43);
lean_ctor_set(x_381, 1, x_85);
lean_ctor_set(x_381, 2, x_127);
lean_ctor_set(x_381, 3, x_295);
lean_ctor_set(x_381, 4, x_337);
x_382 = lean_unbox(x_169);
lean_dec(x_169);
lean_ctor_set_uint8(x_381, sizeof(void*)*5, x_382);
x_383 = lean_unbox(x_211);
lean_dec(x_211);
lean_ctor_set_uint8(x_381, sizeof(void*)*5 + 1, x_383);
x_384 = lean_unbox(x_253);
lean_dec(x_253);
lean_ctor_set_uint8(x_381, sizeof(void*)*5 + 2, x_384);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_381);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_339, 0, x_385);
return x_339;
}
else
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; 
x_386 = lean_ctor_get(x_339, 0);
lean_inc(x_386);
lean_dec(x_339);
x_387 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_387, 0, x_43);
lean_ctor_set(x_387, 1, x_85);
lean_ctor_set(x_387, 2, x_127);
lean_ctor_set(x_387, 3, x_295);
lean_ctor_set(x_387, 4, x_337);
x_388 = lean_unbox(x_169);
lean_dec(x_169);
lean_ctor_set_uint8(x_387, sizeof(void*)*5, x_388);
x_389 = lean_unbox(x_211);
lean_dec(x_211);
lean_ctor_set_uint8(x_387, sizeof(void*)*5 + 1, x_389);
x_390 = lean_unbox(x_253);
lean_dec(x_253);
lean_ctor_set_uint8(x_387, sizeof(void*)*5 + 2, x_390);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_387);
lean_ctor_set(x_391, 1, x_386);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
return x_392;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661__spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3661_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 2, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SerialMessage_toMessage(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_32 = lean_ctor_get(x_17, 4);
lean_inc(x_32);
if (x_2 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_33 = x_41;
goto block_40;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_17, 2);
lean_inc(x_42);
x_33 = x_42;
goto block_40;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("\n", 1, 1);
x_5 = lean_string_append(x_3, x_4);
lean_dec(x_4);
return x_5;
}
block_16:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_instDecidableEqPos(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_11 = lean_string_utf8_prev(x_7, x_8);
lean_dec(x_8);
x_12 = lean_string_utf8_get(x_7, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(10u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_12, x_14);
if (x_15 == 0)
{
x_3 = x_7;
goto block_6;
}
else
{
if (x_10 == 0)
{
return x_7;
}
else
{
x_3 = x_7;
goto block_6;
}
}
}
else
{
lean_dec(x_8);
x_3 = x_7;
goto block_6;
}
}
block_31:
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*5 + 1);
switch (x_20) {
case 0:
{
lean_dec(x_18);
lean_dec(x_17);
x_7 = x_19;
goto block_16;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_mk_string_unchecked("warning: ", 9, 9);
x_24 = l_Lean_mkErrorStringWithPos(x_21, x_22, x_23, x_18);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_19);
lean_dec(x_19);
x_7 = x_25;
goto block_16;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_mk_string_unchecked("error: ", 7, 7);
x_29 = l_Lean_mkErrorStringWithPos(x_26, x_27, x_28, x_18);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_19);
lean_dec(x_19);
x_7 = x_30;
goto block_16;
}
}
}
block_40:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_17, 3);
lean_inc(x_34);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = lean_string_dec_eq(x_34, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_mk_string_unchecked(":\n", 2, 2);
x_38 = lean_string_append(x_34, x_37);
lean_dec(x_37);
x_39 = lean_string_append(x_38, x_32);
lean_dec(x_32);
x_18 = x_33;
x_19 = x_39;
goto block_31;
}
else
{
lean_dec(x_34);
x_18 = x_33;
x_19 = x_32;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_SerialMessage_toString(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_SerialMessage_toString(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SerialMessage_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SerialMessage_instToString___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_Lean_MessageData_kind(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Message_kind(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Lean_MessageData_toString(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 2, x_12);
x_15 = l_Lean_MessageData_kind(x_3);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 2, x_24);
x_27 = l_Lean_MessageData_kind(x_3);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_37; lean_object* x_38; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_MessageData_toString(x_4, x_3);
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
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
if (x_2 == 0)
{
lean_object* x_45; 
lean_dec(x_1);
x_45 = lean_box(0);
x_38 = x_45;
goto block_44;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_38 = x_46;
goto block_44;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_string_unchecked("\n", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
if (lean_is_scalar(x_8)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_8;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
block_24:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_byte_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_instDecidableEqPos(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_18 = lean_string_utf8_prev(x_14, x_15);
lean_dec(x_15);
x_19 = lean_string_utf8_get(x_14, x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(10u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_19, x_21);
if (x_22 == 0)
{
x_9 = x_14;
goto block_13;
}
else
{
if (x_17 == 0)
{
lean_object* x_23; 
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
x_9 = x_14;
goto block_13;
}
}
}
else
{
lean_dec(x_15);
x_9 = x_14;
goto block_13;
}
}
block_36:
{
switch (x_27) {
case 0:
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
x_14 = x_29;
goto block_24;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_mk_string_unchecked("warning: ", 9, 9);
x_31 = l_Lean_mkErrorStringWithPos(x_25, x_26, x_30, x_28);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_29);
lean_dec(x_29);
x_14 = x_32;
goto block_24;
}
default: 
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_mk_string_unchecked("error: ", 7, 7);
x_34 = l_Lean_mkErrorStringWithPos(x_25, x_26, x_33, x_28);
lean_dec(x_33);
x_35 = lean_string_append(x_34, x_29);
lean_dec(x_29);
x_14 = x_35;
goto block_24;
}
}
}
block_44:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = lean_string_dec_eq(x_37, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_mk_string_unchecked(":\n", 2, 2);
x_42 = lean_string_append(x_37, x_41);
lean_dec(x_41);
x_43 = lean_string_append(x_42, x_6);
lean_dec(x_6);
x_28 = x_38;
x_29 = x_43;
goto block_36;
}
else
{
lean_dec(x_37);
x_28 = x_38;
x_29 = x_6;
goto block_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Message_toString(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Lean_MessageData_toString(x_3, x_2);
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
x_8 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName___lam__0___boxed), 1, 0);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_MessageData_kind(x_3);
lean_dec(x_3);
x_17 = lean_mk_string_unchecked("fileName", 8, 8);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("pos", 3, 3);
x_23 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_mk_string_unchecked("endPos", 6, 6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_27 = x_73;
goto block_72;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_11, 0);
lean_inc(x_74);
lean_dec(x_11);
x_75 = l___private_Lean_Data_Position_0__Lean_toJsonPosition____x40_Lean_Data_Position___hyg_237_(x_74);
x_27 = x_75;
goto block_72;
}
block_72:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = lean_mk_string_unchecked("keepFullRange", 13, 13);
x_31 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_31, 0, x_12);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_20);
x_34 = lean_mk_string_unchecked("severity", 8, 8);
x_35 = l___private_Lean_Message_0__Lean_toJsonMessageSeverity____x40_Lean_Message___hyg_125_(x_13);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_20);
x_38 = lean_mk_string_unchecked("isSilent", 8, 8);
x_39 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_39, 0, x_14);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_20);
x_42 = lean_mk_string_unchecked("caption", 7, 7);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_15);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_20);
x_46 = lean_mk_string_unchecked("data", 4, 4);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_20);
x_50 = lean_mk_string_unchecked("kind", 4, 4);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_16, x_52, x_8);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_20);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_37);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_29);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_25);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_21);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_mk_empty_array_with_capacity(x_67);
x_69 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_66, x_68);
x_70 = l_Lean_Json_mkObj(x_69);
if (lean_is_scalar(x_7)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_7;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
return x_71;
}
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set_usize(x_6, 4, x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_MessageLog_empty() {
_start:
{
lean_object* x_1; lean_object* x_2; size_t x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_usize_of_nat(x_2);
x_4 = lean_usize_to_nat(x_3);
x_5 = lean_nat_pow(x_1, x_4);
lean_dec(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_usize(x_11, 4, x_3);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_msgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentArray_append___redArg(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
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
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasUnreported(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_PersistentArray_push___redArg(x_4, x_1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_PersistentArray_append___redArg(x_3, x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l_Lean_PersistentArray_append___redArg(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_RBTree_union___redArg(x_9, x_10, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_MessageLog_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_append), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
lean_dec(x_6);
x_8 = lean_box(x_7);
if (lean_obj_tag(x_8) == 2)
{
uint8_t x_9; 
x_9 = lean_unbox(x_5);
return x_9;
}
else
{
lean_dec(x_8);
if (x_4 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_5);
return x_14;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
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
x_8 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0(x_2, x_6, x_7);
return x_8;
}
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
return x_12;
}
else
{
if (x_12 == 0)
{
lean_dec(x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_usize_of_nat(x_10);
x_14 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_15 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(x_9, x_13, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = lean_usize_of_nat(x_5);
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(x_4, x_8, x_9);
return x_10;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4(x_1, x_6);
lean_dec(x_6);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5 + 1);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = lean_unbox(x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0(x_11);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_6);
return x_17;
}
}
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
if (x_13 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_usize_of_nat(x_11);
x_15 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_16 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5(x_1, x_10, x_14, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
return x_4;
}
else
{
if (x_8 == 0)
{
lean_dec(x_7);
return x_4;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = lean_usize_of_nat(x_6);
x_10 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5(x_1, x_5, x_9, x_10);
return x_11;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0_spec__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4_spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at___Lean_MessageLog_hasErrors_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_Lean_PersistentArray_append___redArg(x_2, x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_unsigned_to_nat(5u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_nat_pow(x_5, x_8);
lean_dec(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set_usize(x_15, 4, x_7);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_16 = lean_box(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_21 = lean_box(1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 2);
x_23 = lean_ctor_get(x_5, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 4);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_20);
x_26 = lean_unbox(x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_26);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 2, x_22);
x_8 = x_25;
goto block_14;
}
else
{
lean_dec(x_16);
x_8 = x_5;
goto block_14;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
x_7 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0(x_4, x_6, x_3);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0(x_9, x_11, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_16, x_18, x_15);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_21, x_23, x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_5, x_7, x_4);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_usize(x_12, 4, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_usize_to_nat(x_4);
x_6 = lean_nat_pow(x_2, x_5);
lean_dec(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_usize(x_12, 4, x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_16 = lean_box(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_21 = lean_box(0);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 2);
x_23 = lean_ctor_get(x_5, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 4);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_20);
x_26 = lean_unbox(x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_26);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 2, x_22);
x_8 = x_25;
goto block_14;
}
else
{
lean_dec(x_16);
x_8 = x_5;
goto block_14;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
x_7 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0(x_4, x_6, x_3);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0(x_9, x_11, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_16, x_18, x_15);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_21, x_23, x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_5, x_7, x_4);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_usize(x_12, 4, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_usize_to_nat(x_4);
x_6 = lean_nat_pow(x_2, x_5);
lean_dec(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_usize(x_12, 4, x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_PersistentArray_mapMAux___at___Lean_PersistentArray_mapM___at___Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0(x_6, x_4);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*5 + 1);
x_14 = lean_box(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_push___redArg(x_4, x_12);
x_5 = x_15;
goto block_10;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_4;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_7 = lean_usize_shift_right(x_2, x_3);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get(x_6, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_shift_left(x_11, x_3);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_2, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_sub(x_3, x_16);
x_18 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_9, x_14, x_17, x_4);
lean_dec(x_9);
x_19 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_18;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_18;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0(x_5, x_23, x_24, x_18);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_usize_to_nat(x_2);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_4;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_4;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_26, x_31, x_32, x_4);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_4);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_4);
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_usize_to_nat(x_4);
x_6 = lean_nat_pow(x_2, x_5);
lean_dec(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_usize(x_12, 4, x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_14 = l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0(x_13, x_12, x_11);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at___Lean_MessageLog_getInfoMessages_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_getInfoMessages(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_PersistentArray_forM___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageLog_forM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_toList(lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_toArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toArray(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(1);
x_3 = l_Lean_MessageData_ofFormat(x_2);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l_Lean_MessageData_nestD(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofExpr(x_1);
x_3 = l_Lean_indentD(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("「", 3, 1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_mk_string_unchecked("」", 3, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instAddMessageContextOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_7);
lean_ctor_set(x_13, 4, x_8);
lean_ctor_set(x_13, 5, x_9);
lean_ctor_set(x_13, 6, x_10);
lean_ctor_set(x_13, 7, x_11);
lean_ctor_set(x_13, 8, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(5u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_to_nat(x_17);
x_19 = lean_nat_pow(x_15, x_18);
lean_dec(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = lean_usize_to_nat(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_5);
lean_ctor_set_usize(x_24, 4, x_17);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_4);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_apply_2(x_3, lean_box(0), x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addMessageContextPartial___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_5);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_3);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addMessageContextFull___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next(x_1, x_3);
x_13 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_12);
x_2 = x_12;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = l_List_reverse___redArg(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lean_stringToMessageData_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_stringToMessageData_spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = l_Lean_MessageData_ofFormat(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_String_split___at___Lean_stringToMessageData_spec__0(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lean_stringToMessageData_spec__2(x_2, x_3);
x_5 = lean_box(1);
x_6 = l_Lean_MessageData_ofFormat(x_5);
x_7 = l_Lean_MessageData_joinSep(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lean_stringToMessageData_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lean_stringToMessageData_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lean_stringToMessageData_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormat), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_2);
lean_closure_set(x_3, 4, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataOfToFormat___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToMessageDataExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataName() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofName), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_stringToMessageData___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataSyntax() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofSyntax(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataTSyntax___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToMessageDataTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormat), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_instCoeMVarId___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToMessageDataMessageData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_1, x_2, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataList___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_to_list(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_1, x_3, x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Array_ofSubarray___redArg(x_2);
x_4 = lean_array_to_list(x_3);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop(lean_box(0), lean_box(0), x_1, x_4, x_5);
x_7 = l_Lean_MessageData_ofList(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataSubarray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataSubarray___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_MessageData_ofFormat(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_mk_string_unchecked("some (", 6, 6);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_8);
x_9 = l_Lean_MessageData_ofFormat(x_2);
x_10 = lean_apply_1(x_1, x_7);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked(")", 1, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_mk_string_unchecked("some (", 6, 6);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_apply_1(x_1, x_16);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked(")", 1, 1);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_mk_string_unchecked(",", 1, 1);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_7);
x_11 = lean_box(1);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_1(x_2, x_6);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_paren(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_apply_1(x_1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_apply_1(x_2, x_18);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_paren(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instToMessageDataProd___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_MessageData_ofFormat(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_MessageData_ofExpr(x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOptionExpr___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_termM_x21__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("termM!_", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("m!", 2, 2);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("termM!_", 7, 7);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_mk_string_unchecked("MessageData", 11, 11);
lean_inc(x_18);
x_19 = l_String_toSubstring_x27(x_18);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr1(x_18);
lean_inc(x_16);
lean_inc(x_17);
x_21 = l_Lean_addMacroScope(x_17, x_20, x_16);
lean_inc(x_4);
x_22 = l_Lean_Name_mkStr2(x_4, x_18);
x_23 = lean_box(0);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_15);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_mk_string_unchecked("toMessageData", 13, 13);
lean_inc(x_30);
x_31 = l_String_toSubstring_x27(x_30);
lean_inc(x_30);
x_32 = l_Lean_Name_mkStr1(x_30);
x_33 = l_Lean_addMacroScope(x_17, x_32, x_16);
x_34 = lean_mk_string_unchecked("ToMessageData", 13, 13);
x_35 = l_Lean_Name_mkStr3(x_4, x_34, x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Lean_TSyntax_expandInterpolatedStr(x_11, x_29, x_38, x_2, x_3);
lean_dec(x_11);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
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
else
{
uint8_t x_44; 
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
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_to_list(x_1);
x_3 = lean_mk_string_unchecked("\n\n", 2, 2);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = l_Lean_MessageData_joinSep(x_2, x_4);
x_6 = l_Lean_indentD(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_elab_environment_of_kernel_env(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_7);
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_7);
x_14 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set(x_14, 8, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_3);
x_16 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_mk_string_unchecked("(kernel) declaration type mismatch, '", 37, 37);
x_5 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_6 = l_Lean_MessageData_ofName(x_2);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("' has type", 10, 10);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_indentExpr(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("\nbut it is expected to have type", 32, 32);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_indentExpr(x_3);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(5u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_nat_pow(x_8, x_11);
lean_dec(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_mk_empty_array_with_capacity(x_14);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_usize(x_18, 4, x_10);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("(kernel) unknown constant '", 27, 27);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_22);
x_24 = lean_mk_string_unchecked("'", 1, 1);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_4, x_20, x_2, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_to_nat(x_34);
x_36 = lean_nat_pow(x_32, x_35);
lean_dec(x_35);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = lean_usize_to_nat(x_37);
x_39 = lean_mk_empty_array_with_capacity(x_38);
lean_dec(x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set_usize(x_42, 4, x_34);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_mk_string_unchecked("(kernel) unknown constant '", 27, 27);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = l_Lean_MessageData_ofName(x_29);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_28, x_44, x_2, x_51);
return x_52;
}
}
case 1:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
x_56 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_unsigned_to_nat(5u);
x_60 = lean_usize_of_nat(x_59);
x_61 = lean_usize_to_nat(x_60);
x_62 = lean_nat_pow(x_58, x_61);
lean_dec(x_61);
x_63 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_64 = lean_usize_to_nat(x_63);
x_65 = lean_mk_empty_array_with_capacity(x_64);
lean_dec(x_64);
lean_inc(x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set_usize(x_68, 4, x_60);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_mk_string_unchecked("(kernel) constant has already been declared '", 45, 45);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
x_75 = l_Lean_MessageData_ofConstName(x_55, x_74);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_72);
x_76 = lean_mk_string_unchecked("'", 1, 1);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_54, x_70, x_2, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; lean_object* x_87; lean_object* x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_1);
x_82 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_unsigned_to_nat(5u);
x_86 = lean_usize_of_nat(x_85);
x_87 = lean_usize_to_nat(x_86);
x_88 = lean_nat_pow(x_84, x_87);
lean_dec(x_87);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = lean_usize_to_nat(x_89);
x_91 = lean_mk_empty_array_with_capacity(x_90);
lean_dec(x_90);
lean_inc(x_91);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set_usize(x_94, 4, x_86);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_95);
x_97 = lean_mk_string_unchecked("(kernel) constant has already been declared '", 45, 45);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
x_99 = lean_box(1);
x_100 = lean_unbox(x_99);
x_101 = l_Lean_MessageData_ofConstName(x_81, x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("'", 1, 1);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_80, x_96, x_2, x_105);
return x_106;
}
}
case 2:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_108 = lean_ctor_get(x_1, 0);
x_109 = lean_ctor_get(x_1, 1);
x_110 = lean_ctor_get(x_1, 2);
x_111 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_unsigned_to_nat(5u);
x_115 = lean_usize_of_nat(x_114);
x_116 = lean_usize_to_nat(x_115);
x_117 = lean_nat_pow(x_113, x_116);
lean_dec(x_116);
x_118 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_119 = lean_usize_to_nat(x_118);
x_120 = lean_mk_empty_array_with_capacity(x_119);
lean_dec(x_119);
lean_inc(x_120);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_122);
lean_ctor_set_usize(x_123, 4, x_115);
x_124 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 2, x_124);
lean_ctor_set(x_1, 1, x_123);
lean_ctor_set(x_1, 0, x_112);
switch (lean_obj_tag(x_109)) {
case 1:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_109, 0);
lean_inc(x_125);
lean_dec(x_109);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 2);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_110, x_127, x_128);
x_130 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_108, x_1, x_2, x_129);
return x_130;
}
case 2:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_109, 0);
lean_inc(x_131);
lean_dec(x_109);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 2);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_110, x_133, x_134);
x_136 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_108, x_1, x_2, x_135);
return x_136;
}
default: 
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_110);
lean_dec(x_109);
x_137 = lean_mk_string_unchecked("(kernel) declaration type mismatch", 34, 34);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_108, x_1, x_2, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; lean_object* x_149; lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
x_143 = lean_ctor_get(x_1, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_1);
x_144 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_unsigned_to_nat(5u);
x_148 = lean_usize_of_nat(x_147);
x_149 = lean_usize_to_nat(x_148);
x_150 = lean_nat_pow(x_146, x_149);
lean_dec(x_149);
x_151 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_152 = lean_usize_to_nat(x_151);
x_153 = lean_mk_empty_array_with_capacity(x_152);
lean_dec(x_152);
lean_inc(x_153);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_153);
lean_ctor_set(x_156, 2, x_155);
lean_ctor_set(x_156, 3, x_155);
lean_ctor_set_usize(x_156, 4, x_148);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_157);
switch (lean_obj_tag(x_142)) {
case 1:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_142, 0);
lean_inc(x_159);
lean_dec(x_142);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 2);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_143, x_161, x_162);
x_164 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_141, x_158, x_2, x_163);
return x_164;
}
case 2:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_142, 0);
lean_inc(x_165);
lean_dec(x_142);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_143, x_167, x_168);
x_170 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_141, x_158, x_2, x_169);
return x_170;
}
default: 
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_143);
lean_dec(x_142);
x_171 = lean_mk_string_unchecked("(kernel) declaration type mismatch", 34, 34);
x_172 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = l_Lean_MessageData_ofFormat(x_172);
x_174 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_141, x_158, x_2, x_173);
return x_174;
}
}
}
}
case 3:
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_1);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; size_t x_183; lean_object* x_184; lean_object* x_185; size_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_176 = lean_ctor_get(x_1, 0);
x_177 = lean_ctor_get(x_1, 1);
x_178 = lean_ctor_get(x_1, 2);
lean_dec(x_178);
x_179 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_unsigned_to_nat(2u);
x_182 = lean_unsigned_to_nat(5u);
x_183 = lean_usize_of_nat(x_182);
x_184 = lean_usize_to_nat(x_183);
x_185 = lean_nat_pow(x_181, x_184);
lean_dec(x_184);
x_186 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_187 = lean_usize_to_nat(x_186);
x_188 = lean_mk_empty_array_with_capacity(x_187);
lean_dec(x_187);
lean_inc(x_188);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_190);
lean_ctor_set_usize(x_191, 4, x_183);
x_192 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 2, x_192);
lean_ctor_set(x_1, 1, x_191);
lean_ctor_set(x_1, 0, x_180);
x_193 = lean_mk_string_unchecked("(kernel) declaration has metavariables '", 40, 40);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
x_195 = lean_box(1);
x_196 = lean_unbox(x_195);
x_197 = l_Lean_MessageData_ofConstName(x_177, x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_mk_string_unchecked("'", 1, 1);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
x_202 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_176, x_1, x_2, x_201);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; size_t x_209; lean_object* x_210; lean_object* x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_203 = lean_ctor_get(x_1, 0);
x_204 = lean_ctor_get(x_1, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_1);
x_205 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = lean_unsigned_to_nat(2u);
x_208 = lean_unsigned_to_nat(5u);
x_209 = lean_usize_of_nat(x_208);
x_210 = lean_usize_to_nat(x_209);
x_211 = lean_nat_pow(x_207, x_210);
lean_dec(x_210);
x_212 = lean_usize_of_nat(x_211);
lean_dec(x_211);
x_213 = lean_usize_to_nat(x_212);
x_214 = lean_mk_empty_array_with_capacity(x_213);
lean_dec(x_213);
lean_inc(x_214);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_unsigned_to_nat(0u);
x_217 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_216);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set_usize(x_217, 4, x_209);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_219, 0, x_206);
lean_ctor_set(x_219, 1, x_217);
lean_ctor_set(x_219, 2, x_218);
x_220 = lean_mk_string_unchecked("(kernel) declaration has metavariables '", 40, 40);
x_221 = l_Lean_stringToMessageData(x_220);
lean_dec(x_220);
x_222 = lean_box(1);
x_223 = lean_unbox(x_222);
x_224 = l_Lean_MessageData_ofConstName(x_204, x_223);
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_mk_string_unchecked("'", 1, 1);
x_227 = l_Lean_stringToMessageData(x_226);
lean_dec(x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
x_229 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_203, x_219, x_2, x_228);
return x_229;
}
}
case 4:
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_1);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_238; lean_object* x_239; lean_object* x_240; size_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_231 = lean_ctor_get(x_1, 0);
x_232 = lean_ctor_get(x_1, 1);
x_233 = lean_ctor_get(x_1, 2);
lean_dec(x_233);
x_234 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = lean_unsigned_to_nat(2u);
x_237 = lean_unsigned_to_nat(5u);
x_238 = lean_usize_of_nat(x_237);
x_239 = lean_usize_to_nat(x_238);
x_240 = lean_nat_pow(x_236, x_239);
lean_dec(x_239);
x_241 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_242 = lean_usize_to_nat(x_241);
x_243 = lean_mk_empty_array_with_capacity(x_242);
lean_dec(x_242);
lean_inc(x_243);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_unsigned_to_nat(0u);
x_246 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_243);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_245);
lean_ctor_set_usize(x_246, 4, x_238);
x_247 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_235);
x_248 = lean_mk_string_unchecked("(kernel) declaration has free variables '", 41, 41);
x_249 = l_Lean_stringToMessageData(x_248);
lean_dec(x_248);
x_250 = lean_box(1);
x_251 = lean_unbox(x_250);
x_252 = l_Lean_MessageData_ofConstName(x_232, x_251);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_mk_string_unchecked("'", 1, 1);
x_255 = l_Lean_stringToMessageData(x_254);
lean_dec(x_254);
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_255);
x_257 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_231, x_1, x_2, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; size_t x_264; lean_object* x_265; lean_object* x_266; size_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_258 = lean_ctor_get(x_1, 0);
x_259 = lean_ctor_get(x_1, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_1);
x_260 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = lean_unsigned_to_nat(2u);
x_263 = lean_unsigned_to_nat(5u);
x_264 = lean_usize_of_nat(x_263);
x_265 = lean_usize_to_nat(x_264);
x_266 = lean_nat_pow(x_262, x_265);
lean_dec(x_265);
x_267 = lean_usize_of_nat(x_266);
lean_dec(x_266);
x_268 = lean_usize_to_nat(x_267);
x_269 = lean_mk_empty_array_with_capacity(x_268);
lean_dec(x_268);
lean_inc(x_269);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_269);
lean_ctor_set(x_272, 2, x_271);
lean_ctor_set(x_272, 3, x_271);
lean_ctor_set_usize(x_272, 4, x_264);
x_273 = lean_box(0);
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_261);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set(x_274, 2, x_273);
x_275 = lean_mk_string_unchecked("(kernel) declaration has free variables '", 41, 41);
x_276 = l_Lean_stringToMessageData(x_275);
lean_dec(x_275);
x_277 = lean_box(1);
x_278 = lean_unbox(x_277);
x_279 = l_Lean_MessageData_ofConstName(x_259, x_278);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_276);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_mk_string_unchecked("'", 1, 1);
x_282 = l_Lean_stringToMessageData(x_281);
lean_dec(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_282);
x_284 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_258, x_274, x_2, x_283);
return x_284;
}
}
case 5:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_285 = lean_ctor_get(x_1, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_1, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_1, 2);
lean_inc(x_287);
lean_dec(x_1);
x_288 = lean_mk_string_unchecked("(kernel) function expected", 26, 26);
x_289 = l_Lean_stringToMessageData(x_288);
lean_dec(x_288);
x_290 = l_Lean_indentExpr(x_287);
x_291 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_mk_string_unchecked("", 0, 0);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_295 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_285, x_286, x_2, x_294);
return x_295;
}
case 6:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_296 = lean_ctor_get(x_1, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_1, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_1, 2);
lean_inc(x_298);
lean_dec(x_1);
x_299 = lean_mk_string_unchecked("(kernel) type expected", 22, 22);
x_300 = l_Lean_stringToMessageData(x_299);
lean_dec(x_299);
x_301 = l_Lean_indentExpr(x_298);
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_mk_string_unchecked("", 0, 0);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_304);
x_306 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_296, x_297, x_2, x_305);
return x_306;
}
case 7:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_307 = lean_ctor_get(x_1, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_1, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_1, 2);
lean_inc(x_309);
lean_dec(x_1);
x_310 = lean_mk_string_unchecked("(kernel) let-declaration type mismatch '", 40, 40);
x_311 = l_Lean_stringToMessageData(x_310);
lean_dec(x_310);
x_312 = l_Lean_MessageData_ofName(x_309);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_mk_string_unchecked("'", 1, 1);
x_315 = l_Lean_stringToMessageData(x_314);
lean_dec(x_314);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_315);
x_317 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_307, x_308, x_2, x_316);
return x_317;
}
case 8:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_318 = lean_ctor_get(x_1, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_1, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_1, 2);
lean_inc(x_320);
lean_dec(x_1);
x_321 = lean_mk_string_unchecked("(kernel) type mismatch at", 25, 25);
x_322 = l_Lean_stringToMessageData(x_321);
lean_dec(x_321);
x_323 = l_Lean_indentExpr(x_320);
x_324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_mk_string_unchecked("", 0, 0);
x_326 = l_Lean_stringToMessageData(x_325);
lean_dec(x_325);
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_326);
x_328 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_318, x_319, x_2, x_327);
return x_328;
}
case 9:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_329 = lean_ctor_get(x_1, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_1, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_1, 2);
lean_inc(x_331);
x_332 = lean_ctor_get(x_1, 3);
lean_inc(x_332);
x_333 = lean_ctor_get(x_1, 4);
lean_inc(x_333);
lean_dec(x_1);
x_334 = lean_mk_string_unchecked("(kernel) application type mismatch", 34, 34);
x_335 = l_Lean_stringToMessageData(x_334);
lean_dec(x_334);
x_336 = l_Lean_indentExpr(x_331);
x_337 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_mk_string_unchecked("\nargument has type", 18, 18);
x_339 = l_Lean_stringToMessageData(x_338);
lean_dec(x_338);
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_indentExpr(x_333);
x_342 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_mk_string_unchecked("\nbut function has type", 22, 22);
x_344 = l_Lean_stringToMessageData(x_343);
lean_dec(x_343);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_indentExpr(x_332);
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_mk_string_unchecked("", 0, 0);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
x_351 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_329, x_330, x_2, x_350);
return x_351;
}
case 10:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_352 = lean_ctor_get(x_1, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_1, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_1, 2);
lean_inc(x_354);
lean_dec(x_1);
x_355 = lean_mk_string_unchecked("(kernel) invalid projection", 27, 27);
x_356 = l_Lean_stringToMessageData(x_355);
lean_dec(x_355);
x_357 = l_Lean_indentExpr(x_354);
x_358 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_mk_string_unchecked("", 0, 0);
x_360 = l_Lean_stringToMessageData(x_359);
lean_dec(x_359);
x_361 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_360);
x_362 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_352, x_353, x_2, x_361);
return x_362;
}
case 11:
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_1);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; size_t x_371; lean_object* x_372; lean_object* x_373; size_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_364 = lean_ctor_get(x_1, 0);
x_365 = lean_ctor_get(x_1, 1);
x_366 = lean_ctor_get(x_1, 2);
x_367 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_unsigned_to_nat(2u);
x_370 = lean_unsigned_to_nat(5u);
x_371 = lean_usize_of_nat(x_370);
x_372 = lean_usize_to_nat(x_371);
x_373 = lean_nat_pow(x_369, x_372);
lean_dec(x_372);
x_374 = lean_usize_of_nat(x_373);
lean_dec(x_373);
x_375 = lean_usize_to_nat(x_374);
x_376 = lean_mk_empty_array_with_capacity(x_375);
lean_dec(x_375);
lean_inc(x_376);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_376);
x_378 = lean_unsigned_to_nat(0u);
x_379 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_376);
lean_ctor_set(x_379, 2, x_378);
lean_ctor_set(x_379, 3, x_378);
lean_ctor_set_usize(x_379, 4, x_371);
x_380 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 2, x_380);
lean_ctor_set(x_1, 1, x_379);
lean_ctor_set(x_1, 0, x_368);
x_381 = lean_mk_string_unchecked("(kernel) type of theorem '", 26, 26);
x_382 = l_Lean_stringToMessageData(x_381);
lean_dec(x_381);
x_383 = lean_box(1);
x_384 = lean_unbox(x_383);
x_385 = l_Lean_MessageData_ofConstName(x_365, x_384);
x_386 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_386, 0, x_382);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_mk_string_unchecked("' is not a proposition", 22, 22);
x_388 = l_Lean_stringToMessageData(x_387);
lean_dec(x_387);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_indentExpr(x_366);
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_mk_string_unchecked("", 0, 0);
x_393 = l_Lean_stringToMessageData(x_392);
lean_dec(x_392);
x_394 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_393);
x_395 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_364, x_1, x_2, x_394);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; size_t x_403; lean_object* x_404; lean_object* x_405; size_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_396 = lean_ctor_get(x_1, 0);
x_397 = lean_ctor_get(x_1, 1);
x_398 = lean_ctor_get(x_1, 2);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_1);
x_399 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_399);
x_401 = lean_unsigned_to_nat(2u);
x_402 = lean_unsigned_to_nat(5u);
x_403 = lean_usize_of_nat(x_402);
x_404 = lean_usize_to_nat(x_403);
x_405 = lean_nat_pow(x_401, x_404);
lean_dec(x_404);
x_406 = lean_usize_of_nat(x_405);
lean_dec(x_405);
x_407 = lean_usize_to_nat(x_406);
x_408 = lean_mk_empty_array_with_capacity(x_407);
lean_dec(x_407);
lean_inc(x_408);
x_409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_409, 0, x_408);
x_410 = lean_unsigned_to_nat(0u);
x_411 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_408);
lean_ctor_set(x_411, 2, x_410);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_usize(x_411, 4, x_403);
x_412 = lean_box(0);
x_413 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_413, 0, x_400);
lean_ctor_set(x_413, 1, x_411);
lean_ctor_set(x_413, 2, x_412);
x_414 = lean_mk_string_unchecked("(kernel) type of theorem '", 26, 26);
x_415 = l_Lean_stringToMessageData(x_414);
lean_dec(x_414);
x_416 = lean_box(1);
x_417 = lean_unbox(x_416);
x_418 = l_Lean_MessageData_ofConstName(x_397, x_417);
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_415);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_mk_string_unchecked("' is not a proposition", 22, 22);
x_421 = l_Lean_stringToMessageData(x_420);
lean_dec(x_420);
x_422 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_indentExpr(x_398);
x_424 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_mk_string_unchecked("", 0, 0);
x_426 = l_Lean_stringToMessageData(x_425);
lean_dec(x_425);
x_427 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_426);
x_428 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_396, x_413, x_2, x_427);
return x_428;
}
}
case 12:
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_2);
x_429 = lean_ctor_get(x_1, 0);
lean_inc(x_429);
lean_dec(x_1);
x_430 = lean_mk_string_unchecked("(kernel) ", 9, 9);
x_431 = l_Lean_stringToMessageData(x_430);
lean_dec(x_430);
x_432 = l_Lean_stringToMessageData(x_429);
lean_dec(x_429);
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_mk_string_unchecked("", 0, 0);
x_435 = l_Lean_stringToMessageData(x_434);
lean_dec(x_434);
x_436 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
case 13:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_2);
x_437 = lean_mk_string_unchecked("(kernel) deterministic timeout", 30, 30);
x_438 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_438, 0, x_437);
x_439 = l_Lean_MessageData_ofFormat(x_438);
return x_439;
}
case 14:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_2);
x_440 = lean_mk_string_unchecked("(kernel) excessive memory consumption detected", 46, 46);
x_441 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_442 = l_Lean_MessageData_ofFormat(x_441);
return x_442;
}
case 15:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_2);
x_443 = lean_mk_string_unchecked("(kernel) deep recursion detected", 32, 32);
x_444 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_444, 0, x_443);
x_445 = l_Lean_MessageData_ofFormat(x_444);
return x_445;
}
default: 
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_2);
x_446 = lean_mk_string_unchecked("(kernel) interrupted", 20, 20);
x_447 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_448 = l_Lean_MessageData_ofFormat(x_447);
return x_448;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; double x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_float_of_nat(x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_float(x_8, sizeof(void*)*2, x_5);
lean_ctor_set_float(x_8, sizeof(void*)*2 + 8, x_5);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2 + 16, x_9);
x_10 = lean_apply_1(x_1, x_2);
x_11 = lean_mk_empty_array_with_capacity(x_4);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_toTraceElem___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PPExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Message(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Position(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instBEqMessageSeverity = _init_l_Lean_instBEqMessageSeverity();
lean_mark_persistent(l_Lean_instBEqMessageSeverity);
l_Lean_instToJsonMessageSeverity = _init_l_Lean_instToJsonMessageSeverity();
lean_mark_persistent(l_Lean_instToJsonMessageSeverity);
l_Lean_instFromJsonMessageSeverity = _init_l_Lean_instFromJsonMessageSeverity();
lean_mark_persistent(l_Lean_instFromJsonMessageSeverity);
l_Lean_instInhabitedMessageData = _init_l_Lean_instInhabitedMessageData();
lean_mark_persistent(l_Lean_instInhabitedMessageData);
l_Lean_instImpl____x40_Lean_Message___hyg_606_ = _init_l_Lean_instImpl____x40_Lean_Message___hyg_606_();
lean_mark_persistent(l_Lean_instImpl____x40_Lean_Message___hyg_606_);
l_Lean_instTypeNameMessageData = _init_l_Lean_instTypeNameMessageData();
lean_mark_persistent(l_Lean_instTypeNameMessageData);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
res = l_Lean_MessageData_initFn____x40_Lean_Message___hyg_1428_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_MessageData_maxTraceChildren = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_MessageData_maxTraceChildren);
lean_dec_ref(res);
l_Lean_MessageData_instAppend = _init_l_Lean_MessageData_instAppend();
lean_mark_persistent(l_Lean_MessageData_instAppend);
l_Lean_MessageData_instCoeString = _init_l_Lean_MessageData_instCoeString();
lean_mark_persistent(l_Lean_MessageData_instCoeString);
l_Lean_MessageData_instCoeFormat = _init_l_Lean_MessageData_instCoeFormat();
lean_mark_persistent(l_Lean_MessageData_instCoeFormat);
l_Lean_MessageData_instCoeLevel = _init_l_Lean_MessageData_instCoeLevel();
lean_mark_persistent(l_Lean_MessageData_instCoeLevel);
l_Lean_MessageData_instCoeExpr = _init_l_Lean_MessageData_instCoeExpr();
lean_mark_persistent(l_Lean_MessageData_instCoeExpr);
l_Lean_MessageData_instCoeName = _init_l_Lean_MessageData_instCoeName();
lean_mark_persistent(l_Lean_MessageData_instCoeName);
l_Lean_MessageData_instCoeSyntax = _init_l_Lean_MessageData_instCoeSyntax();
lean_mark_persistent(l_Lean_MessageData_instCoeSyntax);
l_Lean_MessageData_instCoeMVarId = _init_l_Lean_MessageData_instCoeMVarId();
lean_mark_persistent(l_Lean_MessageData_instCoeMVarId);
l_Lean_MessageData_instCoeOptionExpr = _init_l_Lean_MessageData_instCoeOptionExpr();
lean_mark_persistent(l_Lean_MessageData_instCoeOptionExpr);
l_Lean_MessageData_instCoeArrayExpr = _init_l_Lean_MessageData_instCoeArrayExpr();
lean_mark_persistent(l_Lean_MessageData_instCoeArrayExpr);
l_Lean_MessageData_instCoeList = _init_l_Lean_MessageData_instCoeList();
lean_mark_persistent(l_Lean_MessageData_instCoeList);
l_Lean_MessageData_instCoeListExpr = _init_l_Lean_MessageData_instCoeListExpr();
lean_mark_persistent(l_Lean_MessageData_instCoeListExpr);
l_Lean_instToJsonSerialMessage = _init_l_Lean_instToJsonSerialMessage();
lean_mark_persistent(l_Lean_instToJsonSerialMessage);
l_Lean_instFromJsonSerialMessage = _init_l_Lean_instFromJsonSerialMessage();
lean_mark_persistent(l_Lean_instFromJsonSerialMessage);
l_Lean_SerialMessage_instToString = _init_l_Lean_SerialMessage_instToString();
lean_mark_persistent(l_Lean_SerialMessage_instToString);
l_Lean_instInhabitedMessageLog = _init_l_Lean_instInhabitedMessageLog();
lean_mark_persistent(l_Lean_instInhabitedMessageLog);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
l_Lean_MessageLog_instAppend = _init_l_Lean_MessageLog_instAppend();
lean_mark_persistent(l_Lean_MessageLog_instAppend);
l_Lean_instToMessageDataExpr = _init_l_Lean_instToMessageDataExpr();
lean_mark_persistent(l_Lean_instToMessageDataExpr);
l_Lean_instToMessageDataLevel = _init_l_Lean_instToMessageDataLevel();
lean_mark_persistent(l_Lean_instToMessageDataLevel);
l_Lean_instToMessageDataName = _init_l_Lean_instToMessageDataName();
lean_mark_persistent(l_Lean_instToMessageDataName);
l_Lean_instToMessageDataString = _init_l_Lean_instToMessageDataString();
lean_mark_persistent(l_Lean_instToMessageDataString);
l_Lean_instToMessageDataSyntax = _init_l_Lean_instToMessageDataSyntax();
lean_mark_persistent(l_Lean_instToMessageDataSyntax);
l_Lean_instToMessageDataFormat = _init_l_Lean_instToMessageDataFormat();
lean_mark_persistent(l_Lean_instToMessageDataFormat);
l_Lean_instToMessageDataMVarId = _init_l_Lean_instToMessageDataMVarId();
lean_mark_persistent(l_Lean_instToMessageDataMVarId);
l_Lean_instToMessageDataMessageData = _init_l_Lean_instToMessageDataMessageData();
lean_mark_persistent(l_Lean_instToMessageDataMessageData);
l_Lean_instToMessageDataOptionExpr = _init_l_Lean_instToMessageDataOptionExpr();
lean_mark_persistent(l_Lean_instToMessageDataOptionExpr);
l_Lean_termM_x21__ = _init_l_Lean_termM_x21__();
lean_mark_persistent(l_Lean_termM_x21__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
