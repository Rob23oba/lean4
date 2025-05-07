// Lean compiler output
// Module: Lean.Widget.InteractiveDiagnostic
// Imports: Lean.Linter.UnusedVariables Lean.Server.Utils Lean.Widget.InteractiveGoal
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_dec____x40_Lean_Widget_InteractiveGoal___hyg_1148_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1088_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object*);
lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611____boxed(lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(uint8_t, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__10____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__8____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc____x40_Lean_Widget_Types___hyg_3_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__13____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1140_(lean_object*);
lean_object* l_Lean_Widget_tagCodeInfos_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__12____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1956_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Widget_goalToInteractive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__9____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonRange____x40_Lean_Data_Lsp_Basic___hyg_667_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instTypeNameLazyTraceChildren;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__11____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
lean_object* l_Lean_Widget_InteractiveGoal_pretty(lean_object*);
uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__14____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1113_;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedMsgEmbed;
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object*);
lean_object* l_MonadExcept_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedEmbedFmt;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_264_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_isUnusedVariableWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(lean_object*);
extern lean_object* l_Lean_Widget_instImpl____x40_Lean_Widget_Basic___hyg_28_;
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Except_instMonad___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_enc____x40_Lean_Widget_InteractiveGoal___hyg_1148_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_ExceptT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2608_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object*, lean_object*);
lean_object* l_Subarray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570____boxed(lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2696_;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_2250__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1279_;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_207_;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_MessageData_maxTraceChildren;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__7____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("strict", 6, 6);
x_8 = l_Lean_Json_parseTagged(x_1, x_7, x_2, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Except_orElseLazy___redArg(x_8, x_4);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___redArg(x_12, x_4);
lean_dec(x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_5, x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
x_19 = l_Except_orElseLazy___redArg(x_8, x_4);
lean_dec(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_5, x_20, x_21);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___redArg(x_24, x_4);
lean_dec(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("lazy", 4, 4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_3);
x_8 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_6);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Except_orElseLazy___redArg(x_8, x_7);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___redArg(x_12, x_7);
lean_dec(x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_3, x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
x_19 = l_Except_orElseLazy___redArg(x_8, x_7);
lean_dec(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_3, x_20, x_21);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___redArg(x_24, x_7);
lean_dec(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_207_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_mk_string_unchecked("strict", 6, 6);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_mk_string_unchecked("lazy", 4, 4);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_264_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_7, x_6, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_3, 0, x_10);
x_11 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_3);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_12);
x_14 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_3);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_17, x_16, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_22);
lean_dec(x_22);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_2(x_27, x_26, x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_3, 0, x_30);
x_31 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_3);
lean_dec(x_3);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_3, 0, x_32);
x_34 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_3);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_apply_2(x_37, x_36, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_42);
lean_dec(x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(x_3);
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
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_12, x_11, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_free_object(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_9, 0, x_18);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_2(x_22, x_21, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_apply_2(x_33, x_32, x_4);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_free_object(x_9);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_9, 0, x_39);
lean_ctor_set(x_34, 0, x_9);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
lean_ctor_set(x_9, 0, x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_9);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_apply_2(x_43, x_42, x_4);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_48);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4_), 6, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Widget", 6, 6);
x_3 = lean_mk_string_unchecked("LazyTraceChildren", 17, 17);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Widget_instTypeNameLazyTraceChildren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
return x_1;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_mk_string_unchecked("trace", 5, 5);
x_8 = lean_unsigned_to_nat(5u);
x_9 = lean_mk_string_unchecked("indent", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("cls", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("msg", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("collapsed", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("children", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_empty_array_with_capacity(x_8);
x_20 = lean_array_push(x_19, x_10);
x_21 = lean_array_push(x_20, x_12);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Json_parseTagged(x_1, x_7, x_8, x_25);
lean_dec(x_25);
lean_dec(x_7);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Except_orElseLazy___redArg(x_26, x_2);
lean_dec(x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Except_orElseLazy___redArg(x_30, x_2);
lean_dec(x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_35 = lean_array_get(x_3, x_33, x_34);
lean_inc(x_3);
x_36 = lean_array_get(x_3, x_33, x_4);
lean_inc(x_3);
x_37 = lean_array_get(x_3, x_33, x_5);
x_38 = lean_unsigned_to_nat(3u);
lean_inc(x_3);
x_39 = lean_array_get(x_3, x_33, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_array_get(x_3, x_33, x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_26, 0, x_42);
x_43 = l_Except_orElseLazy___redArg(x_26, x_2);
lean_dec(x_26);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
lean_dec(x_26);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_46 = lean_array_get(x_3, x_44, x_45);
lean_inc(x_3);
x_47 = lean_array_get(x_3, x_44, x_4);
lean_inc(x_3);
x_48 = lean_array_get(x_3, x_44, x_5);
x_49 = lean_unsigned_to_nat(3u);
lean_inc(x_3);
x_50 = lean_array_get(x_3, x_44, x_49);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_array_get(x_3, x_44, x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Except_orElseLazy___redArg(x_54, x_2);
lean_dec(x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("widget", 6, 6);
x_7 = lean_unsigned_to_nat(2u);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_7);
x_9 = lean_mk_string_unchecked("wi", 2, 2);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("alt", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_empty_array_with_capacity(x_7);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Json_parseTagged(x_1, x_6, x_7, x_16);
lean_dec(x_16);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Except_orElseLazy___redArg(x_17, x_8);
lean_dec(x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Except_orElseLazy___redArg(x_21, x_8);
lean_dec(x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_26 = lean_array_get(x_3, x_24, x_25);
x_27 = lean_array_get(x_3, x_24, x_4);
lean_dec(x_4);
lean_dec(x_24);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_17, 0, x_28);
x_29 = l_Except_orElseLazy___redArg(x_17, x_8);
lean_dec(x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_32 = lean_array_get(x_3, x_30, x_31);
x_33 = lean_array_get(x_3, x_30, x_4);
lean_dec(x_4);
lean_dec(x_30);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Except_orElseLazy___redArg(x_35, x_8);
lean_dec(x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("expr", 4, 4);
x_8 = l_Lean_Json_parseTagged(x_1, x_7, x_2, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Except_orElseLazy___redArg(x_8, x_4);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___redArg(x_12, x_4);
lean_dec(x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_5, x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
x_19 = l_Except_orElseLazy___redArg(x_8, x_4);
lean_dec(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_5, x_20, x_21);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___redArg(x_24, x_4);
lean_dec(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("goal", 4, 4);
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_3);
x_9 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_7);
lean_dec(x_4);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_3, x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = l_Except_orElseLazy___redArg(x_9, x_8);
lean_dec(x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_3, x_21, x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Except_orElseLazy___redArg(x_25, x_8);
lean_dec(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1113_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("expr", 4, 4);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_mk_string_unchecked("goal", 4, 4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
case 2:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_mk_string_unchecked("widget", 6, 6);
x_18 = lean_mk_string_unchecked("wi", 2, 2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_18);
x_19 = lean_mk_string_unchecked("alt", 3, 3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Lean_Json_mkObj(x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("widget", 6, 6);
x_31 = lean_mk_string_unchecked("wi", 2, 2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_mk_string_unchecked("alt", 3, 3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Json_mkObj(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = l_Lean_Json_mkObj(x_40);
return x_41;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 4);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_mk_string_unchecked("trace", 5, 5);
x_48 = lean_mk_string_unchecked("indent", 6, 6);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_mk_string_unchecked("cls", 3, 3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
x_52 = lean_mk_string_unchecked("msg", 3, 3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
x_54 = lean_mk_string_unchecked("collapsed", 9, 9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
x_56 = lean_mk_string_unchecked("children", 8, 8);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_46);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Json_mkObj(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
x_67 = l_Lean_Json_mkObj(x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1279_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_7, x_8, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_5, x_7, x_4, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_array_size(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_11, x_7, x_10);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_13);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_array_size(x_15);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_17, x_7, x_15);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 0, x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_array_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_23, x_25, x_22, x_2);
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
x_30 = lean_array_size(x_27);
x_31 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_30, x_25, x_27);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_33);
lean_dec(x_33);
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
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
x_39 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_box(0), x_38, x_37, x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_1, 0, x_41);
x_42 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_1);
lean_dec(x_1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
lean_ctor_set(x_1, 0, x_43);
x_45 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_1);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
x_49 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_box(0), x_48, x_47, x_2);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_54 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_210_(x_53);
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_7 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_6, x_5, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_9);
lean_ctor_set(x_1, 0, x_10);
x_11 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_12);
lean_ctor_set(x_1, 0, x_14);
x_15 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_19 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_18, x_17, x_2);
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
x_23 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_24);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
case 1:
{
uint8_t x_27; 
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc____x40_Lean_Widget_InteractiveGoal___hyg_1148_(x_28, x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_1, 0, x_31);
x_32 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_1);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_1, 0, x_33);
x_35 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc____x40_Lean_Widget_InteractiveGoal___hyg_1148_(x_37, x_2);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
case 2:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_Widget_instRpcEncodableWidgetInstance_enc____x40_Lean_Widget_Types___hyg_3_(x_45, x_2);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_3, x_46, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_52);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_53);
x_54 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_47);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_55);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_57);
x_58 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_3, x_46, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_63);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_67);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_74 = lean_ctor_get(x_1, 3);
lean_inc(x_74);
lean_dec(x_1);
x_75 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_3, x_72, x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(x_74, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570____boxed), 1, 0);
x_82 = lean_box(1);
x_83 = l_Lean_JsonNumber_fromNat(x_70);
x_84 = lean_unbox(x_82);
x_85 = l_Lean_Name_toString(x_71, x_84, x_81);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_76);
x_89 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_89, 0, x_73);
x_90 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_89);
lean_ctor_set(x_90, 4, x_80);
x_91 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_90);
lean_ctor_set(x_78, 0, x_91);
return x_78;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_78, 0);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_78);
x_94 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570____boxed), 1, 0);
x_95 = lean_box(1);
x_96 = l_Lean_JsonNumber_fromNat(x_70);
x_97 = lean_unbox(x_95);
x_98 = l_Lean_Name_toString(x_71, x_97, x_94);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_96);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_98);
x_101 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_76);
x_102 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_102, 0, x_73);
x_103 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_102);
lean_ctor_set(x_103, 4, x_92);
x_104 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1116_(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_93);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
lean_inc(x_4);
x_14 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_13, x_12, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_20, x_2, x_18);
x_2 = x_23;
x_3 = x_24;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_92_(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(x_11, x_13, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_size(x_16);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_17, x_13, x_16, x_2);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_free_object(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 0);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_23);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_14);
return x_25;
}
}
}
else
{
lean_object* x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_array_size(x_26);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_27, x_13, x_26, x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_32);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_36 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_37 = lean_unsigned_to_nat(80u);
x_38 = l_Lean_Json_pretty(x_9, x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked("'", 1, 1);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_41);
return x_3;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_3);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
x_45 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(x_44, x_43, x_2);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_free_object(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_8, 0, x_50);
lean_ctor_set(x_45, 0, x_8);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
lean_ctor_set(x_8, 0, x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_8);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
lean_dec(x_8);
x_54 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
x_55 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(x_54, x_53, x_2);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
lean_dec(x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 4)
{
lean_object* x_65; size_t x_66; lean_object* x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_array_size(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_usize_of_nat(x_67);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1614__spec__0_spec__0(x_66, x_68, x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_array_size(x_70);
x_73 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_72, x_68, x_70, x_2);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_71;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_81 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_82 = lean_unsigned_to_nat(80u);
x_83 = l_Lean_Json_pretty(x_64, x_82);
x_84 = lean_string_append(x_81, x_83);
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("'", 1, 1);
x_86 = lean_string_append(x_84, x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_63, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_89 = x_63;
} else {
 lean_dec_ref(x_63);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_;
x_91 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(x_90, x_88, x_2);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_89;
}
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_769_(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_free_object(x_7);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_17 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_16, x_15, x_2);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_free_object(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_7, 0, x_22);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
lean_ctor_set(x_7, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_7);
return x_24;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_32 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_31, x_30, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
case 1:
{
uint8_t x_40; 
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec____x40_Lean_Widget_InteractiveGoal___hyg_1148_(x_41, x_2);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_free_object(x_7);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_42, 0);
lean_ctor_set(x_7, 0, x_47);
lean_ctor_set(x_42, 0, x_7);
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
lean_ctor_set(x_7, 0, x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_7);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_7, 0);
lean_inc(x_50);
lean_dec(x_7);
x_51 = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec____x40_Lean_Widget_InteractiveGoal___hyg_1148_(x_50, x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
case 2:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
x_62 = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(x_60);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_free_object(x_7);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_61);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_free_object(x_7);
lean_dec(x_8);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_8, x_71, x_2);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec(x_66);
lean_free_object(x_7);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_72, 0);
lean_ctor_set(x_7, 1, x_77);
lean_ctor_set(x_7, 0, x_66);
lean_ctor_set(x_72, 0, x_7);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
lean_dec(x_72);
lean_ctor_set(x_7, 1, x_78);
lean_ctor_set(x_7, 0, x_66);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_7);
return x_79;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_7, 0);
x_81 = lean_ctor_get(x_7, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_7);
x_82 = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_2);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_8);
lean_dec(x_2);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_8, x_91, x_2);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_86);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_96);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
default: 
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_7, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_7, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_7, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_7, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_7, 4);
lean_inc(x_104);
lean_dec(x_7);
x_105 = l_Lean_Json_getNat_x3f(x_100);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_139; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
lean_dec(x_105);
lean_inc(x_101);
x_139 = l_Lean_Json_getStr_x3f(x_101);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_139);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_139, 0);
x_145 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_146 = lean_string_dec_eq(x_144, x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_String_toName(x_144);
x_148 = l_Lean_Name_isAnonymous(x_147);
if (x_148 == 0)
{
lean_free_object(x_139);
lean_dec(x_101);
x_110 = x_147;
goto block_138;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_2);
x_149 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_150 = lean_unsigned_to_nat(80u);
x_151 = l_Lean_Json_pretty(x_101, x_150);
x_152 = lean_string_append(x_149, x_151);
lean_dec(x_151);
x_153 = lean_mk_string_unchecked("'", 1, 1);
x_154 = lean_string_append(x_152, x_153);
lean_dec(x_153);
lean_ctor_set_tag(x_139, 0);
lean_ctor_set(x_139, 0, x_154);
return x_139;
}
}
else
{
lean_object* x_155; 
lean_free_object(x_139);
lean_dec(x_144);
lean_dec(x_101);
x_155 = lean_box(0);
x_110 = x_155;
goto block_138;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_139, 0);
lean_inc(x_156);
lean_dec(x_139);
x_157 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_158 = lean_string_dec_eq(x_156, x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_String_toName(x_156);
x_160 = l_Lean_Name_isAnonymous(x_159);
if (x_160 == 0)
{
lean_dec(x_101);
x_110 = x_159;
goto block_138;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_159);
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_2);
x_161 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_162 = lean_unsigned_to_nat(80u);
x_163 = l_Lean_Json_pretty(x_101, x_162);
x_164 = lean_string_append(x_161, x_163);
lean_dec(x_163);
x_165 = lean_mk_string_unchecked("'", 1, 1);
x_166 = lean_string_append(x_164, x_165);
lean_dec(x_165);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_dec(x_156);
lean_dec(x_101);
x_168 = lean_box(0);
x_110 = x_168;
goto block_138;
}
}
}
block_138:
{
lean_object* x_111; 
x_111 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_fromJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_407____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(x_102);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec(x_111);
lean_inc(x_2);
x_116 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_box(0), lean_box(0), x_8, x_115, x_2);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
return x_116;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
lean_dec(x_116);
x_121 = l_Lean_Json_getBool_x3f(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_120);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_104);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
lean_dec(x_121);
x_126 = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0(x_104, x_2);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_110);
lean_dec(x_109);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_132, 0, x_109);
lean_ctor_set(x_132, 1, x_110);
lean_ctor_set(x_132, 2, x_120);
lean_ctor_set(x_132, 3, x_131);
x_133 = lean_unbox(x_125);
lean_dec(x_125);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_133);
lean_ctor_set(x_126, 0, x_132);
return x_126;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
lean_dec(x_126);
x_135 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_135, 0, x_109);
lean_ctor_set(x_135, 1, x_110);
lean_ctor_set(x_135, 2, x_120);
lean_ctor_set(x_135, 3, x_134);
x_136 = lean_unbox(x_125);
lean_dec(x_125);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_136);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_135);
return x_137;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Widget_instRpcEncodableMsgEmbed_enc___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableStrictOrLazy_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_4____at___Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570__spec__0_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableMsgEmbed() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1956_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_2 = lean_mk_string_unchecked("range", 5, 5);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_2250__spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("fullRange", 9, 9);
lean_inc(x_1);
x_6 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("severity", 8, 8);
lean_inc(x_1);
x_9 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("isSilent", 8, 8);
lean_inc(x_1);
x_12 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("code", 4, 4);
lean_inc(x_1);
x_15 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("source", 6, 6);
lean_inc(x_1);
x_18 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("message", 7, 7);
lean_inc(x_1);
x_21 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_2250__spec__1(x_1, x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("tags", 4, 4);
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("leanTags", 8, 8);
lean_inc(x_1);
x_27 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("relatedInformation", 18, 18);
lean_inc(x_1);
x_30 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("data", 4, 4);
x_33 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_32);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 2, x_10);
lean_ctor_set(x_36, 3, x_13);
lean_ctor_set(x_36, 4, x_16);
lean_ctor_set(x_36, 5, x_19);
lean_ctor_set(x_36, 6, x_22);
lean_ctor_set(x_36, 7, x_25);
lean_ctor_set(x_36, 8, x_28);
lean_ctor_set(x_36, 9, x_31);
lean_ctor_set(x_36, 10, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_7);
lean_ctor_set(x_38, 2, x_10);
lean_ctor_set(x_38, 3, x_13);
lean_ctor_set(x_38, 4, x_16);
lean_ctor_set(x_38, 5, x_19);
lean_ctor_set(x_38, 6, x_22);
lean_ctor_set(x_38, 7, x_25);
lean_ctor_set(x_38, 8, x_28);
lean_ctor_set(x_38, 9, x_31);
lean_ctor_set(x_38, 10, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2608_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1956_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_2 = lean_mk_string_unchecked("range", 5, 5);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("fullRange", 9, 9);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_7, x_8);
x_10 = lean_mk_string_unchecked("severity", 8, 8);
x_11 = lean_ctor_get(x_1, 2);
x_12 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_10, x_11);
x_13 = lean_mk_string_unchecked("isSilent", 8, 8);
x_14 = lean_ctor_get(x_1, 3);
x_15 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_13, x_14);
x_16 = lean_mk_string_unchecked("code", 4, 4);
x_17 = lean_ctor_get(x_1, 4);
x_18 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_16, x_17);
x_19 = lean_mk_string_unchecked("source", 6, 6);
x_20 = lean_ctor_get(x_1, 5);
x_21 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_19, x_20);
x_22 = lean_mk_string_unchecked("message", 7, 7);
x_23 = lean_ctor_get(x_1, 6);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_mk_string_unchecked("tags", 4, 4);
x_27 = lean_ctor_get(x_1, 7);
x_28 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_26, x_27);
x_29 = lean_mk_string_unchecked("leanTags", 8, 8);
x_30 = lean_ctor_get(x_1, 8);
x_31 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_29, x_30);
x_32 = lean_mk_string_unchecked("relatedInformation", 18, 18);
x_33 = lean_ctor_get(x_1, 9);
x_34 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_32, x_33);
x_35 = lean_mk_string_unchecked("data", 4, 4);
x_36 = lean_ctor_get(x_1, 10);
x_37 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_35, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
x_52 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_49, x_51);
x_53 = l_Lean_Json_mkObj(x_52);
return x_53;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2696_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_JsonNumber_fromNat(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_JsonNumber_fromNat(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1088_(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_JsonNumber_fromNat(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_JsonNumber_fromNat(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_331; lean_object* x_332; lean_object* x_361; 
x_4 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 5, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 5, 0);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_11);
x_361 = lean_ctor_get(x_2, 1);
lean_inc(x_361);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_box(0);
x_331 = x_362;
x_332 = x_3;
goto block_360;
}
else
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_361);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_361, 0);
x_365 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_364);
lean_ctor_set(x_361, 0, x_365);
x_331 = x_361;
x_332 = x_3;
goto block_360;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_361, 0);
lean_inc(x_366);
lean_dec(x_361);
x_367 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_366);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_331 = x_368;
x_332 = x_3;
goto block_360;
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 10);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_17);
lean_ctor_set(x_24, 6, x_16);
lean_ctor_set(x_24, 7, x_14);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_21);
lean_ctor_set(x_24, 10, x_23);
x_25 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
block_97:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_2, 9);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_38 = lean_box(0);
x_13 = x_28;
x_14 = x_29;
x_15 = x_35;
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_34;
x_21 = x_38;
x_22 = x_36;
goto block_27;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_42 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_43 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_44 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_45 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_46 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_47 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
lean_inc(x_50);
x_51 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, lean_box(0));
lean_closure_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
lean_inc(x_50);
x_53 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_53, 0, lean_box(0));
lean_closure_set(x_53, 1, lean_box(0));
lean_closure_set(x_53, 2, x_50);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_8);
lean_ctor_set(x_54, 3, x_9);
lean_ctor_set(x_54, 4, x_10);
lean_inc(x_50);
x_55 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, lean_box(0));
lean_closure_set(x_55, 2, x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_size(x_40);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_usize_of_nat(x_58);
x_60 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_56, x_5, x_57, x_59, x_40);
x_61 = lean_apply_1(x_60, x_36);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_64, 0, lean_box(0));
x_65 = lean_array_size(x_62);
x_66 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_50, x_64, x_65, x_59, x_62);
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_37, 0, x_67);
x_13 = x_28;
x_14 = x_29;
x_15 = x_35;
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_34;
x_21 = x_37;
x_22 = x_63;
goto block_27;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
lean_dec(x_37);
x_69 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_70 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_71 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_72 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_73 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_74 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_75 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
lean_inc(x_78);
x_79 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_79, 0, lean_box(0));
lean_closure_set(x_79, 1, lean_box(0));
lean_closure_set(x_79, 2, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_7);
lean_inc(x_78);
x_81 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_81, 0, lean_box(0));
lean_closure_set(x_81, 1, lean_box(0));
lean_closure_set(x_81, 2, x_78);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_8);
lean_ctor_set(x_82, 3, x_9);
lean_ctor_set(x_82, 4, x_10);
lean_inc(x_78);
x_83 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_83, 0, lean_box(0));
lean_closure_set(x_83, 1, lean_box(0));
lean_closure_set(x_83, 2, x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_size(x_68);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_usize_of_nat(x_86);
x_88 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_84, x_5, x_85, x_87, x_68);
x_89 = lean_apply_1(x_88, x_36);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_92, 0, lean_box(0));
x_93 = lean_array_size(x_90);
x_94 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_78, x_92, x_93, x_87, x_90);
x_95 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_13 = x_28;
x_14 = x_29;
x_15 = x_35;
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_34;
x_21 = x_96;
x_22 = x_91;
goto block_27;
}
}
}
block_166:
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_2, 8);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec(x_4);
x_107 = lean_box(0);
x_28 = x_98;
x_29 = x_104;
x_30 = x_99;
x_31 = x_100;
x_32 = x_101;
x_33 = x_102;
x_34 = x_103;
x_35 = x_107;
x_36 = x_105;
goto block_97;
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; size_t x_126; lean_object* x_127; size_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; size_t x_134; lean_object* x_135; lean_object* x_136; 
x_109 = lean_ctor_get(x_106, 0);
x_110 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_111 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_112 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_113 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_114 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_115 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_116 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_111);
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
lean_inc(x_119);
x_120 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_120, 0, lean_box(0));
lean_closure_set(x_120, 1, lean_box(0));
lean_closure_set(x_120, 2, x_119);
lean_inc(x_7);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
lean_inc(x_119);
x_122 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_122, 0, lean_box(0));
lean_closure_set(x_122, 1, lean_box(0));
lean_closure_set(x_122, 2, x_119);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_8);
lean_ctor_set(x_123, 3, x_9);
lean_ctor_set(x_123, 4, x_10);
lean_inc(x_119);
x_124 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_124, 0, lean_box(0));
lean_closure_set(x_124, 1, lean_box(0));
lean_closure_set(x_124, 2, x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_size(x_109);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_usize_of_nat(x_127);
x_129 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_125, x_4, x_126, x_128, x_109);
x_130 = lean_apply_1(x_129, x_105);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_133, 0, lean_box(0));
x_134 = lean_array_size(x_131);
x_135 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_119, x_133, x_134, x_128, x_131);
x_136 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_106, 0, x_136);
x_28 = x_98;
x_29 = x_104;
x_30 = x_99;
x_31 = x_100;
x_32 = x_101;
x_33 = x_102;
x_34 = x_103;
x_35 = x_106;
x_36 = x_132;
goto block_97;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; size_t x_154; lean_object* x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_137 = lean_ctor_get(x_106, 0);
lean_inc(x_137);
lean_dec(x_106);
x_138 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_139 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_140 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_141 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_142 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_143 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_144 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_139);
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_143);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
lean_inc(x_147);
x_148 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_148, 0, lean_box(0));
lean_closure_set(x_148, 1, lean_box(0));
lean_closure_set(x_148, 2, x_147);
lean_inc(x_7);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_7);
lean_inc(x_147);
x_150 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_150, 0, lean_box(0));
lean_closure_set(x_150, 1, lean_box(0));
lean_closure_set(x_150, 2, x_147);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_8);
lean_ctor_set(x_151, 3, x_9);
lean_ctor_set(x_151, 4, x_10);
lean_inc(x_147);
x_152 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_152, 0, lean_box(0));
lean_closure_set(x_152, 1, lean_box(0));
lean_closure_set(x_152, 2, x_147);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_size(x_137);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_usize_of_nat(x_155);
x_157 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_153, x_4, x_154, x_156, x_137);
x_158 = lean_apply_1(x_157, x_105);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_161, 0, lean_box(0));
x_162 = lean_array_size(x_159);
x_163 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_147, x_161, x_162, x_156, x_159);
x_164 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_28 = x_98;
x_29 = x_104;
x_30 = x_99;
x_31 = x_100;
x_32 = x_101;
x_33 = x_102;
x_34 = x_103;
x_35 = x_165;
x_36 = x_160;
goto block_97;
}
}
}
block_273:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_1, 0);
lean_inc(x_173);
lean_dec(x_1);
x_174 = lean_ctor_get(x_2, 6);
lean_inc(x_174);
x_175 = lean_apply_2(x_173, x_174, x_172);
x_176 = lean_ctor_get(x_2, 7);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_6);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_box(0);
x_98 = x_167;
x_99 = x_177;
x_100 = x_171;
x_101 = x_168;
x_102 = x_169;
x_103 = x_170;
x_104 = x_179;
x_105 = x_178;
goto block_166;
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_175);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_176);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; lean_object* x_201; size_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; lean_object* x_209; lean_object* x_210; 
x_182 = lean_ctor_get(x_175, 0);
x_183 = lean_ctor_get(x_175, 1);
x_184 = lean_ctor_get(x_176, 0);
x_185 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_186 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_187 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_188 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_189 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_190 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_191 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
lean_ctor_set(x_175, 1, x_186);
lean_ctor_set(x_175, 0, x_185);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_175);
lean_ctor_set(x_192, 1, x_187);
lean_ctor_set(x_192, 2, x_188);
lean_ctor_set(x_192, 3, x_189);
lean_ctor_set(x_192, 4, x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
lean_inc(x_193);
x_194 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_194, 0, lean_box(0));
lean_closure_set(x_194, 1, lean_box(0));
lean_closure_set(x_194, 2, x_193);
lean_inc(x_7);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_7);
lean_inc(x_193);
x_196 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_196, 0, lean_box(0));
lean_closure_set(x_196, 1, lean_box(0));
lean_closure_set(x_196, 2, x_193);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_197 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_197, 2, x_8);
lean_ctor_set(x_197, 3, x_9);
lean_ctor_set(x_197, 4, x_10);
lean_inc(x_193);
x_198 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_198, 0, lean_box(0));
lean_closure_set(x_198, 1, lean_box(0));
lean_closure_set(x_198, 2, x_193);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_array_size(x_184);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_usize_of_nat(x_201);
x_203 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_199, x_6, x_200, x_202, x_184);
x_204 = lean_apply_1(x_203, x_183);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_207, 0, lean_box(0));
x_208 = lean_array_size(x_205);
x_209 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_193, x_207, x_208, x_202, x_205);
x_210 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_176, 0, x_210);
x_98 = x_167;
x_99 = x_182;
x_100 = x_171;
x_101 = x_168;
x_102 = x_169;
x_103 = x_170;
x_104 = x_176;
x_105 = x_206;
goto block_166;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; size_t x_229; lean_object* x_230; size_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; size_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_211 = lean_ctor_get(x_175, 0);
x_212 = lean_ctor_get(x_175, 1);
x_213 = lean_ctor_get(x_176, 0);
lean_inc(x_213);
lean_dec(x_176);
x_214 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_215 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_216 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_217 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_218 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_219 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_220 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
lean_ctor_set(x_175, 1, x_215);
lean_ctor_set(x_175, 0, x_214);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_175);
lean_ctor_set(x_221, 1, x_216);
lean_ctor_set(x_221, 2, x_217);
lean_ctor_set(x_221, 3, x_218);
lean_ctor_set(x_221, 4, x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
lean_inc(x_222);
x_223 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_223, 0, lean_box(0));
lean_closure_set(x_223, 1, lean_box(0));
lean_closure_set(x_223, 2, x_222);
lean_inc(x_7);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_7);
lean_inc(x_222);
x_225 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_225, 0, lean_box(0));
lean_closure_set(x_225, 1, lean_box(0));
lean_closure_set(x_225, 2, x_222);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_8);
lean_ctor_set(x_226, 3, x_9);
lean_ctor_set(x_226, 4, x_10);
lean_inc(x_222);
x_227 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_227, 0, lean_box(0));
lean_closure_set(x_227, 1, lean_box(0));
lean_closure_set(x_227, 2, x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_size(x_213);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_usize_of_nat(x_230);
x_232 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_228, x_6, x_229, x_231, x_213);
x_233 = lean_apply_1(x_232, x_212);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_236, 0, lean_box(0));
x_237 = lean_array_size(x_234);
x_238 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_222, x_236, x_237, x_231, x_234);
x_239 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_98 = x_167;
x_99 = x_211;
x_100 = x_171;
x_101 = x_168;
x_102 = x_169;
x_103 = x_170;
x_104 = x_240;
x_105 = x_235;
goto block_166;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; size_t x_261; lean_object* x_262; size_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; size_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_241 = lean_ctor_get(x_175, 0);
x_242 = lean_ctor_get(x_175, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_175);
x_243 = lean_ctor_get(x_176, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_244 = x_176;
} else {
 lean_dec_ref(x_176);
 x_244 = lean_box(0);
}
x_245 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_246 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_247 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_248 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_249 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_250 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_251 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_245);
lean_ctor_set(x_252, 1, x_246);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_247);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_249);
lean_ctor_set(x_253, 4, x_250);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
lean_inc(x_254);
x_255 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_255, 0, lean_box(0));
lean_closure_set(x_255, 1, lean_box(0));
lean_closure_set(x_255, 2, x_254);
lean_inc(x_7);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_7);
lean_inc(x_254);
x_257 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_257, 0, lean_box(0));
lean_closure_set(x_257, 1, lean_box(0));
lean_closure_set(x_257, 2, x_254);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_258 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_ctor_set(x_258, 2, x_8);
lean_ctor_set(x_258, 3, x_9);
lean_ctor_set(x_258, 4, x_10);
lean_inc(x_254);
x_259 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_259, 0, lean_box(0));
lean_closure_set(x_259, 1, lean_box(0));
lean_closure_set(x_259, 2, x_254);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_array_size(x_243);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_usize_of_nat(x_262);
x_264 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_260, x_6, x_261, x_263, x_243);
x_265 = lean_apply_1(x_264, x_242);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_268, 0, lean_box(0));
x_269 = lean_array_size(x_266);
x_270 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_254, x_268, x_269, x_263, x_266);
x_271 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_271, 0, x_270);
if (lean_is_scalar(x_244)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_244;
}
lean_ctor_set(x_272, 0, x_271);
x_98 = x_167;
x_99 = x_241;
x_100 = x_171;
x_101 = x_168;
x_102 = x_169;
x_103 = x_170;
x_104 = x_272;
x_105 = x_267;
goto block_166;
}
}
}
block_287:
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_2, 5);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = lean_box(0);
x_167 = x_274;
x_168 = x_277;
x_169 = x_275;
x_170 = x_276;
x_171 = x_280;
x_172 = x_278;
goto block_273;
}
else
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_279);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_279, 0);
x_283 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_279, 0, x_283);
x_167 = x_274;
x_168 = x_277;
x_169 = x_275;
x_170 = x_276;
x_171 = x_279;
x_172 = x_278;
goto block_273;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_279, 0);
lean_inc(x_284);
lean_dec(x_279);
x_285 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_167 = x_274;
x_168 = x_277;
x_169 = x_275;
x_170 = x_276;
x_171 = x_286;
x_172 = x_278;
goto block_273;
}
}
}
block_294:
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_291);
x_274 = x_288;
x_275 = x_289;
x_276 = x_290;
x_277 = x_293;
x_278 = x_292;
goto block_287;
}
block_311:
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_2, 4);
lean_inc(x_299);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_box(0);
x_274 = x_295;
x_275 = x_297;
x_276 = x_296;
x_277 = x_300;
x_278 = x_298;
goto block_287;
}
else
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
lean_dec(x_299);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = l_Lean_JsonNumber_fromInt(x_303);
lean_ctor_set_tag(x_301, 2);
lean_ctor_set(x_301, 0, x_304);
x_288 = x_295;
x_289 = x_297;
x_290 = x_296;
x_291 = x_301;
x_292 = x_298;
goto block_294;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_301, 0);
lean_inc(x_305);
lean_dec(x_301);
x_306 = l_Lean_JsonNumber_fromInt(x_305);
x_307 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_288 = x_295;
x_289 = x_297;
x_290 = x_296;
x_291 = x_307;
x_292 = x_298;
goto block_294;
}
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_301);
if (x_308 == 0)
{
lean_ctor_set_tag(x_301, 3);
x_288 = x_295;
x_289 = x_297;
x_290 = x_296;
x_291 = x_301;
x_292 = x_298;
goto block_294;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_301, 0);
lean_inc(x_309);
lean_dec(x_301);
x_310 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_288 = x_295;
x_289 = x_297;
x_290 = x_296;
x_291 = x_310;
x_292 = x_298;
goto block_294;
}
}
}
}
block_325:
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_2, 3);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_box(0);
x_295 = x_312;
x_296 = x_313;
x_297 = x_316;
x_298 = x_314;
goto block_311;
}
else
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_318 = lean_ctor_get(x_315, 0);
x_319 = lean_alloc_ctor(1, 0, 1);
x_320 = lean_unbox(x_318);
lean_dec(x_318);
lean_ctor_set_uint8(x_319, 0, x_320);
lean_ctor_set(x_315, 0, x_319);
x_295 = x_312;
x_296 = x_313;
x_297 = x_315;
x_298 = x_314;
goto block_311;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_315, 0);
lean_inc(x_321);
lean_dec(x_315);
x_322 = lean_alloc_ctor(1, 0, 1);
x_323 = lean_unbox(x_321);
lean_dec(x_321);
lean_ctor_set_uint8(x_322, 0, x_323);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_322);
x_295 = x_312;
x_296 = x_313;
x_297 = x_324;
x_298 = x_314;
goto block_311;
}
}
}
block_330:
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_327);
x_312 = x_326;
x_313 = x_329;
x_314 = x_328;
goto block_325;
}
block_360:
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_2, 2);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; 
x_334 = lean_box(0);
x_312 = x_331;
x_313 = x_334;
x_314 = x_332;
goto block_325;
}
else
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_333);
if (x_335 == 0)
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_333, 0);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
switch (x_337) {
case 0:
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_unsigned_to_nat(1u);
x_339 = l_Lean_JsonNumber_fromNat(x_338);
lean_ctor_set_tag(x_333, 2);
lean_ctor_set(x_333, 0, x_339);
x_326 = x_331;
x_327 = x_333;
x_328 = x_332;
goto block_330;
}
case 1:
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_unsigned_to_nat(2u);
x_341 = l_Lean_JsonNumber_fromNat(x_340);
lean_ctor_set_tag(x_333, 2);
lean_ctor_set(x_333, 0, x_341);
x_326 = x_331;
x_327 = x_333;
x_328 = x_332;
goto block_330;
}
case 2:
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_unsigned_to_nat(3u);
x_343 = l_Lean_JsonNumber_fromNat(x_342);
lean_ctor_set_tag(x_333, 2);
lean_ctor_set(x_333, 0, x_343);
x_326 = x_331;
x_327 = x_333;
x_328 = x_332;
goto block_330;
}
default: 
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_unsigned_to_nat(4u);
x_345 = l_Lean_JsonNumber_fromNat(x_344);
lean_ctor_set_tag(x_333, 2);
lean_ctor_set(x_333, 0, x_345);
x_326 = x_331;
x_327 = x_333;
x_328 = x_332;
goto block_330;
}
}
}
else
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_333, 0);
lean_inc(x_346);
lean_dec(x_333);
x_347 = lean_unbox(x_346);
lean_dec(x_346);
switch (x_347) {
case 0:
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_unsigned_to_nat(1u);
x_349 = l_Lean_JsonNumber_fromNat(x_348);
x_350 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_350, 0, x_349);
x_326 = x_331;
x_327 = x_350;
x_328 = x_332;
goto block_330;
}
case 1:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_unsigned_to_nat(2u);
x_352 = l_Lean_JsonNumber_fromNat(x_351);
x_353 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_353, 0, x_352);
x_326 = x_331;
x_327 = x_353;
x_328 = x_332;
goto block_330;
}
case 2:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_unsigned_to_nat(3u);
x_355 = l_Lean_JsonNumber_fromNat(x_354);
x_356 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_326 = x_331;
x_327 = x_356;
x_328 = x_332;
goto block_330;
}
default: 
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_unsigned_to_nat(4u);
x_358 = l_Lean_JsonNumber_fromNat(x_357);
x_359 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_326 = x_331;
x_327 = x_359;
x_328 = x_332;
goto block_330;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_5);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_5);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_7);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__7____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__6____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__8____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, lean_box(0));
lean_closure_set(x_12, 4, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__9____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__8____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_6);
lean_closure_set(x_7, 6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__10____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__9____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__11____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__14____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1140_(x_3);
x_6 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_5);
x_7 = lean_apply_1(x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__12____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Json_getNat_x3f(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_10);
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_12, x_15);
lean_dec(x_12);
if (x_16 == 0)
{
lean_free_object(x_10);
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(1);
lean_ctor_set(x_10, 0, x_17);
x_18 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_10);
x_19 = lean_apply_1(x_18, x_4);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
x_21 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_10);
x_22 = lean_apply_1(x_21, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_dec_eq(x_23, x_26);
lean_dec(x_23);
if (x_27 == 0)
{
goto block_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_29);
x_31 = lean_apply_1(x_30, x_4);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_33);
x_35 = lean_apply_1(x_34, x_4);
return x_35;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("unknown LeanDiagnosticTag", 25, 25);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_6);
x_8 = lean_apply_1(x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__13____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Json_getNat_x3f(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_10);
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_12, x_15);
lean_dec(x_12);
if (x_16 == 0)
{
lean_free_object(x_10);
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(1);
lean_ctor_set(x_10, 0, x_17);
x_18 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_10);
x_19 = lean_apply_1(x_18, x_4);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
x_21 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_10);
x_22 = lean_apply_1(x_21, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_dec_eq(x_23, x_26);
lean_dec(x_23);
if (x_27 == 0)
{
goto block_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_29);
x_31 = lean_apply_1(x_30, x_4);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_33);
x_35 = lean_apply_1(x_34, x_4);
return x_35;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_mk_string_unchecked("unknown DiagnosticTag", 21, 21);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_6);
x_8 = lean_apply_1(x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_4 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1956_(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 5, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 3, 1);
lean_closure_set(x_18, 0, x_16);
lean_inc(x_16);
x_19 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_16);
lean_inc(x_16);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__4____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 6, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_16);
lean_inc(x_19);
lean_inc(x_16);
x_21 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__7____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 6, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_19);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__10____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 6, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_19);
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, x_19);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_20);
lean_inc(x_19);
x_27 = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
lean_closure_set(x_27, 2, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
lean_closure_set(x_29, 2, x_19);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_instMonadExceptOfMonadExceptOf___redArg(x_30);
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
x_33 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonRange____x40_Lean_Data_Lsp_Basic___hyg_667_(x_32);
lean_inc(x_31);
lean_inc(x_28);
x_34 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_33);
lean_inc(x_3);
x_35 = lean_apply_1(x_34, x_3);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_518; lean_object* x_519; lean_object* x_572; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_40 = x_35;
} else {
 lean_dec_ref(x_35);
 x_40 = lean_box(0);
}
x_84 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__11____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 1, 0);
lean_inc(x_31);
lean_inc(x_28);
x_85 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__14____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 2);
lean_closure_set(x_85, 0, x_28);
lean_closure_set(x_85, 1, x_31);
lean_inc(x_31);
lean_inc(x_28);
x_168 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__12____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 2);
lean_closure_set(x_168, 0, x_28);
lean_closure_set(x_168, 1, x_31);
lean_inc(x_31);
lean_inc(x_28);
x_250 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__13____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 2);
lean_closure_set(x_250, 0, x_28);
lean_closure_set(x_250, 1, x_31);
x_572 = lean_ctor_get(x_5, 1);
lean_inc(x_572);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
x_573 = lean_box(0);
x_518 = x_573;
x_519 = x_3;
goto block_571;
}
else
{
uint8_t x_574; 
x_574 = !lean_is_exclusive(x_572);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_572, 0);
x_576 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonRange____x40_Lean_Data_Lsp_Basic___hyg_667_(x_575);
lean_inc(x_31);
lean_inc(x_28);
x_577 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_576);
lean_inc(x_3);
x_578 = lean_apply_1(x_577, x_3);
if (lean_obj_tag(x_578) == 0)
{
uint8_t x_579; 
lean_free_object(x_572);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
return x_578;
}
else
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_578, 0);
lean_inc(x_580);
lean_dec(x_578);
x_581 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_581, 0, x_580);
return x_581;
}
}
else
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_578, 0);
lean_inc(x_582);
lean_dec(x_578);
lean_ctor_set(x_572, 0, x_582);
x_518 = x_572;
x_519 = x_3;
goto block_571;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_583 = lean_ctor_get(x_572, 0);
lean_inc(x_583);
lean_dec(x_572);
x_584 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonRange____x40_Lean_Data_Lsp_Basic___hyg_667_(x_583);
lean_inc(x_31);
lean_inc(x_28);
x_585 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_584);
lean_inc(x_3);
x_586 = lean_apply_1(x_585, x_3);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 x_588 = x_586;
} else {
 lean_dec_ref(x_586);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(0, 1, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_587);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_586, 0);
lean_inc(x_590);
lean_dec(x_586);
x_591 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_591, 0, x_590);
x_518 = x_591;
x_519 = x_3;
goto block_571;
}
}
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_51, 5, x_45);
lean_ctor_set(x_51, 6, x_43);
lean_ctor_set(x_51, 7, x_42);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_47);
lean_ctor_set(x_51, 10, x_50);
if (lean_is_scalar(x_40)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_40;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
block_83:
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_5, 10);
lean_inc(x_64);
lean_dec(x_5);
if (lean_obj_tag(x_64) == 0)
{
lean_dec(x_63);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
x_44 = x_57;
x_45 = x_59;
x_46 = x_58;
x_47 = x_62;
x_48 = x_61;
x_49 = x_60;
x_50 = x_64;
goto block_53;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_64, 0);
if (lean_is_scalar(x_6)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_6;
}
lean_ctor_set(x_67, 0, x_66);
x_68 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_67);
x_69 = lean_apply_1(x_68, x_63);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_free_object(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_39);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
lean_ctor_set(x_64, 0, x_73);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
x_44 = x_57;
x_45 = x_59;
x_46 = x_58;
x_47 = x_62;
x_48 = x_61;
x_49 = x_60;
x_50 = x_64;
goto block_53;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
if (lean_is_scalar(x_6)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_6;
}
lean_ctor_set(x_75, 0, x_74);
x_76 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_75);
x_77 = lean_apply_1(x_76, x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_39);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
x_44 = x_57;
x_45 = x_59;
x_46 = x_58;
x_47 = x_62;
x_48 = x_61;
x_49 = x_60;
x_50 = x_82;
goto block_53;
}
}
}
}
block_167:
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_5, 9);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_dec(x_85);
lean_dec(x_84);
x_96 = lean_box(0);
x_54 = x_86;
x_55 = x_87;
x_56 = x_88;
x_57 = x_93;
x_58 = x_90;
x_59 = x_89;
x_60 = x_92;
x_61 = x_91;
x_62 = x_96;
x_63 = x_94;
goto block_83;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_100 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_101 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_102 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_103 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_103, 0, lean_box(0));
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
x_105 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_105, 0, lean_box(0));
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_100);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set(x_106, 4, x_102);
x_107 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_107, 0, lean_box(0));
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
if (lean_obj_tag(x_98) == 4)
{
lean_object* x_109; size_t x_110; lean_object* x_111; size_t x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_98, 0);
lean_inc(x_109);
lean_dec(x_98);
x_110 = lean_array_size(x_109);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_usize_of_nat(x_111);
x_113 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_108, x_84, x_110, x_112, x_109);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_free_object(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
return x_113;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
lean_object* x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_array_size(x_117);
lean_inc(x_28);
x_119 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_85, x_118, x_112, x_117);
lean_inc(x_94);
x_120 = lean_apply_1(x_119, x_94);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
lean_free_object(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
lean_dec(x_120);
lean_ctor_set(x_95, 0, x_124);
x_54 = x_86;
x_55 = x_87;
x_56 = x_88;
x_57 = x_93;
x_58 = x_90;
x_59 = x_89;
x_60 = x_92;
x_61 = x_91;
x_62 = x_95;
x_63 = x_94;
goto block_83;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_108);
lean_free_object(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_125 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_126 = lean_unsigned_to_nat(80u);
x_127 = l_Lean_Json_pretty(x_98, x_126);
x_128 = lean_string_append(x_125, x_127);
lean_dec(x_127);
x_129 = lean_mk_string_unchecked("'", 1, 1);
x_130 = lean_string_append(x_128, x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_95, 0);
lean_inc(x_132);
lean_dec(x_95);
x_133 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_134 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_135 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_136 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_137 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_137, 0, lean_box(0));
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
x_139 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_139, 0, lean_box(0));
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_135);
lean_ctor_set(x_140, 4, x_136);
x_141 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_141, 0, lean_box(0));
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
if (lean_obj_tag(x_132) == 4)
{
lean_object* x_143; size_t x_144; lean_object* x_145; size_t x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_132, 0);
lean_inc(x_143);
lean_dec(x_132);
x_144 = lean_array_size(x_143);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_usize_of_nat(x_145);
x_147 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_142, x_84, x_144, x_146, x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
else
{
lean_object* x_151; size_t x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_array_size(x_151);
lean_inc(x_28);
x_153 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_85, x_152, x_146, x_151);
lean_inc(x_94);
x_154 = lean_apply_1(x_153, x_94);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
lean_dec(x_154);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_54 = x_86;
x_55 = x_87;
x_56 = x_88;
x_57 = x_93;
x_58 = x_90;
x_59 = x_89;
x_60 = x_92;
x_61 = x_91;
x_62 = x_159;
x_63 = x_94;
goto block_83;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_142);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_160 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_161 = lean_unsigned_to_nat(80u);
x_162 = l_Lean_Json_pretty(x_132, x_161);
x_163 = lean_string_append(x_160, x_162);
lean_dec(x_162);
x_164 = lean_mk_string_unchecked("'", 1, 1);
x_165 = lean_string_append(x_163, x_164);
lean_dec(x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
}
block_249:
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_5, 8);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
lean_dec(x_168);
x_178 = lean_box(0);
x_86 = x_169;
x_87 = x_175;
x_88 = x_170;
x_89 = x_172;
x_90 = x_171;
x_91 = x_174;
x_92 = x_173;
x_93 = x_178;
x_94 = x_176;
goto block_167;
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_180 = lean_ctor_get(x_177, 0);
x_181 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_182 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_183 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_184 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_185 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_185, 0, lean_box(0));
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
x_187 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_187, 0, lean_box(0));
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_188, 2, x_182);
lean_ctor_set(x_188, 3, x_183);
lean_ctor_set(x_188, 4, x_184);
x_189 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_189, 0, lean_box(0));
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
if (lean_obj_tag(x_180) == 4)
{
lean_object* x_191; size_t x_192; lean_object* x_193; size_t x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_180, 0);
lean_inc(x_191);
lean_dec(x_180);
x_192 = lean_array_size(x_191);
x_193 = lean_unsigned_to_nat(0u);
x_194 = lean_usize_of_nat(x_193);
lean_inc(x_84);
x_195 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_190, x_84, x_192, x_194, x_191);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
lean_free_object(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
return x_195;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
else
{
lean_object* x_199; size_t x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
lean_dec(x_195);
x_200 = lean_array_size(x_199);
lean_inc(x_28);
x_201 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_168, x_200, x_194, x_199);
lean_inc(x_176);
x_202 = lean_apply_1(x_201, x_176);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
lean_free_object(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
return x_202;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
else
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
lean_dec(x_202);
lean_ctor_set(x_177, 0, x_206);
x_86 = x_169;
x_87 = x_175;
x_88 = x_170;
x_89 = x_172;
x_90 = x_171;
x_91 = x_174;
x_92 = x_173;
x_93 = x_177;
x_94 = x_176;
goto block_167;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_190);
lean_free_object(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_207 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_208 = lean_unsigned_to_nat(80u);
x_209 = l_Lean_Json_pretty(x_180, x_208);
x_210 = lean_string_append(x_207, x_209);
lean_dec(x_209);
x_211 = lean_mk_string_unchecked("'", 1, 1);
x_212 = lean_string_append(x_210, x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_177, 0);
lean_inc(x_214);
lean_dec(x_177);
x_215 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_216 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_217 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_218 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_219 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_219, 0, lean_box(0));
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
x_221 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_221, 0, lean_box(0));
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set(x_222, 2, x_216);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 4, x_218);
x_223 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_223, 0, lean_box(0));
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
if (lean_obj_tag(x_214) == 4)
{
lean_object* x_225; size_t x_226; lean_object* x_227; size_t x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_214, 0);
lean_inc(x_225);
lean_dec(x_214);
x_226 = lean_array_size(x_225);
x_227 = lean_unsigned_to_nat(0u);
x_228 = lean_usize_of_nat(x_227);
lean_inc(x_84);
x_229 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_224, x_84, x_226, x_228, x_225);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
else
{
lean_object* x_233; size_t x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
lean_dec(x_229);
x_234 = lean_array_size(x_233);
lean_inc(x_28);
x_235 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_168, x_234, x_228, x_233);
lean_inc(x_176);
x_236 = lean_apply_1(x_235, x_176);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
lean_dec(x_236);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_86 = x_169;
x_87 = x_175;
x_88 = x_170;
x_89 = x_172;
x_90 = x_171;
x_91 = x_174;
x_92 = x_173;
x_93 = x_241;
x_94 = x_176;
goto block_167;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_224);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_242 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_243 = lean_unsigned_to_nat(80u);
x_244 = l_Lean_Json_pretty(x_214, x_243);
x_245 = lean_string_append(x_242, x_244);
lean_dec(x_244);
x_246 = lean_mk_string_unchecked("'", 1, 1);
x_247 = lean_string_append(x_245, x_246);
lean_dec(x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
}
}
}
block_374:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_1, 1);
lean_inc(x_257);
lean_dec(x_1);
x_258 = lean_ctor_get(x_5, 6);
lean_inc(x_258);
lean_inc(x_256);
x_259 = lean_apply_2(x_257, x_258, x_256);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
return x_259;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
}
else
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_5, 7);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_250);
x_264 = lean_ctor_get(x_259, 0);
lean_inc(x_264);
lean_dec(x_259);
x_265 = lean_box(0);
x_169 = x_251;
x_170 = x_264;
x_171 = x_252;
x_172 = x_255;
x_173 = x_254;
x_174 = x_253;
x_175 = x_265;
x_176 = x_256;
goto block_249;
}
else
{
uint8_t x_266; 
x_266 = !lean_is_exclusive(x_259);
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_263);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_268 = lean_ctor_get(x_259, 0);
x_269 = lean_ctor_get(x_263, 0);
x_270 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_271 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_272 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_273 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_274 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_274, 0, lean_box(0));
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
x_276 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_276, 0, lean_box(0));
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_277, 2, x_271);
lean_ctor_set(x_277, 3, x_272);
lean_ctor_set(x_277, 4, x_273);
x_278 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_278, 0, lean_box(0));
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
if (lean_obj_tag(x_269) == 4)
{
lean_object* x_280; size_t x_281; lean_object* x_282; size_t x_283; lean_object* x_284; 
lean_free_object(x_259);
x_280 = lean_ctor_get(x_269, 0);
lean_inc(x_280);
lean_dec(x_269);
x_281 = lean_array_size(x_280);
x_282 = lean_unsigned_to_nat(0u);
x_283 = lean_usize_of_nat(x_282);
lean_inc(x_84);
x_284 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_279, x_84, x_281, x_283, x_280);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
lean_free_object(x_263);
lean_dec(x_268);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
return x_284;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
else
{
lean_object* x_288; size_t x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_284, 0);
lean_inc(x_288);
lean_dec(x_284);
x_289 = lean_array_size(x_288);
lean_inc(x_28);
x_290 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_250, x_289, x_283, x_288);
lean_inc(x_256);
x_291 = lean_apply_1(x_290, x_256);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
lean_free_object(x_263);
lean_dec(x_268);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
return x_291;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
else
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec(x_291);
lean_ctor_set(x_263, 0, x_295);
x_169 = x_251;
x_170 = x_268;
x_171 = x_252;
x_172 = x_255;
x_173 = x_254;
x_174 = x_253;
x_175 = x_263;
x_176 = x_256;
goto block_249;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_279);
lean_free_object(x_263);
lean_dec(x_268);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_296 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_297 = lean_unsigned_to_nat(80u);
x_298 = l_Lean_Json_pretty(x_269, x_297);
x_299 = lean_string_append(x_296, x_298);
lean_dec(x_298);
x_300 = lean_mk_string_unchecked("'", 1, 1);
x_301 = lean_string_append(x_299, x_300);
lean_dec(x_300);
lean_ctor_set_tag(x_259, 0);
lean_ctor_set(x_259, 0, x_301);
return x_259;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_302 = lean_ctor_get(x_259, 0);
x_303 = lean_ctor_get(x_263, 0);
lean_inc(x_303);
lean_dec(x_263);
x_304 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_305 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_306 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_307 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_308 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_308, 0, lean_box(0));
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_304);
x_310 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_310, 0, lean_box(0));
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_306);
lean_ctor_set(x_311, 4, x_307);
x_312 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_312, 0, lean_box(0));
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
if (lean_obj_tag(x_303) == 4)
{
lean_object* x_314; size_t x_315; lean_object* x_316; size_t x_317; lean_object* x_318; 
lean_free_object(x_259);
x_314 = lean_ctor_get(x_303, 0);
lean_inc(x_314);
lean_dec(x_303);
x_315 = lean_array_size(x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = lean_usize_of_nat(x_316);
lean_inc(x_84);
x_318 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_313, x_84, x_315, x_317, x_314);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_302);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_320 = x_318;
} else {
 lean_dec_ref(x_318);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
else
{
lean_object* x_322; size_t x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_array_size(x_322);
lean_inc(x_28);
x_324 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_250, x_323, x_317, x_322);
lean_inc(x_256);
x_325 = lean_apply_1(x_324, x_256);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_302);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 1, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_326);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_325, 0);
lean_inc(x_329);
lean_dec(x_325);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_169 = x_251;
x_170 = x_302;
x_171 = x_252;
x_172 = x_255;
x_173 = x_254;
x_174 = x_253;
x_175 = x_330;
x_176 = x_256;
goto block_249;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_331 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_332 = lean_unsigned_to_nat(80u);
x_333 = l_Lean_Json_pretty(x_303, x_332);
x_334 = lean_string_append(x_331, x_333);
lean_dec(x_333);
x_335 = lean_mk_string_unchecked("'", 1, 1);
x_336 = lean_string_append(x_334, x_335);
lean_dec(x_335);
lean_ctor_set_tag(x_259, 0);
lean_ctor_set(x_259, 0, x_336);
return x_259;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_337 = lean_ctor_get(x_259, 0);
lean_inc(x_337);
lean_dec(x_259);
x_338 = lean_ctor_get(x_263, 0);
lean_inc(x_338);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_339 = x_263;
} else {
 lean_dec_ref(x_263);
 x_339 = lean_box(0);
}
x_340 = lean_alloc_closure((void*)(l_Except_instMonad___lam__0), 4, 0);
x_341 = lean_alloc_closure((void*)(l_Except_instMonad___lam__1), 4, 0);
x_342 = lean_alloc_closure((void*)(l_Except_instMonad___lam__2___boxed), 4, 0);
x_343 = lean_alloc_closure((void*)(l_Except_instMonad___lam__3___boxed), 4, 0);
x_344 = lean_alloc_closure((void*)(l_Except_map), 5, 1);
lean_closure_set(x_344, 0, lean_box(0));
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_340);
x_346 = lean_alloc_closure((void*)(l_Except_pure), 3, 1);
lean_closure_set(x_346, 0, lean_box(0));
x_347 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set(x_347, 2, x_341);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set(x_347, 4, x_343);
x_348 = lean_alloc_closure((void*)(l_Except_bind), 5, 1);
lean_closure_set(x_348, 0, lean_box(0));
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
if (lean_obj_tag(x_338) == 4)
{
lean_object* x_350; size_t x_351; lean_object* x_352; size_t x_353; lean_object* x_354; 
x_350 = lean_ctor_get(x_338, 0);
lean_inc(x_350);
lean_dec(x_338);
x_351 = lean_array_size(x_350);
x_352 = lean_unsigned_to_nat(0u);
x_353 = lean_usize_of_nat(x_352);
lean_inc(x_84);
x_354 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_349, x_84, x_351, x_353, x_350);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 x_356 = x_354;
} else {
 lean_dec_ref(x_354);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 1, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_355);
return x_357;
}
else
{
lean_object* x_358; size_t x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_354, 0);
lean_inc(x_358);
lean_dec(x_354);
x_359 = lean_array_size(x_358);
lean_inc(x_28);
x_360 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_28, x_250, x_359, x_353, x_358);
lean_inc(x_256);
x_361 = lean_apply_1(x_360, x_256);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_363 = x_361;
} else {
 lean_dec_ref(x_361);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_362);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
lean_dec(x_361);
if (lean_is_scalar(x_339)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_339;
}
lean_ctor_set(x_366, 0, x_365);
x_169 = x_251;
x_170 = x_337;
x_171 = x_252;
x_172 = x_255;
x_173 = x_254;
x_174 = x_253;
x_175 = x_366;
x_176 = x_256;
goto block_249;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_349);
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_367 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_368 = lean_unsigned_to_nat(80u);
x_369 = l_Lean_Json_pretty(x_338, x_368);
x_370 = lean_string_append(x_367, x_369);
lean_dec(x_369);
x_371 = lean_mk_string_unchecked("'", 1, 1);
x_372 = lean_string_append(x_370, x_371);
lean_dec(x_371);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
}
}
block_400:
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_5, 5);
lean_inc(x_380);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_box(0);
x_251 = x_378;
x_252 = x_375;
x_253 = x_377;
x_254 = x_376;
x_255 = x_381;
x_256 = x_379;
goto block_374;
}
else
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_380);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_380, 0);
x_384 = l_Lean_Json_getStr_x3f(x_383);
lean_inc(x_31);
lean_inc(x_28);
x_385 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_384);
lean_inc(x_379);
x_386 = lean_apply_1(x_385, x_379);
if (lean_obj_tag(x_386) == 0)
{
uint8_t x_387; 
lean_free_object(x_380);
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_387 = !lean_is_exclusive(x_386);
if (x_387 == 0)
{
return x_386;
}
else
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_386, 0);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_388);
return x_389;
}
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_386, 0);
lean_inc(x_390);
lean_dec(x_386);
lean_ctor_set(x_380, 0, x_390);
x_251 = x_378;
x_252 = x_375;
x_253 = x_377;
x_254 = x_376;
x_255 = x_380;
x_256 = x_379;
goto block_374;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_380, 0);
lean_inc(x_391);
lean_dec(x_380);
x_392 = l_Lean_Json_getStr_x3f(x_391);
lean_inc(x_31);
lean_inc(x_28);
x_393 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_392);
lean_inc(x_379);
x_394 = lean_apply_1(x_393, x_379);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_396 = x_394;
} else {
 lean_dec_ref(x_394);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(0, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
lean_dec(x_394);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_398);
x_251 = x_378;
x_252 = x_375;
x_253 = x_377;
x_254 = x_376;
x_255 = x_399;
x_256 = x_379;
goto block_374;
}
}
}
}
block_411:
{
if (lean_obj_tag(x_405) == 0)
{
uint8_t x_406; 
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
return x_405;
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_408, 0, x_407);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_405, 0);
lean_inc(x_409);
lean_dec(x_405);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_375 = x_402;
x_376 = x_404;
x_377 = x_403;
x_378 = x_410;
x_379 = x_401;
goto block_400;
}
}
block_426:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_417 = lean_mk_string_unchecked("expected string or integer diagnostic code, got '", 49, 49);
x_418 = lean_unsigned_to_nat(80u);
x_419 = l_Lean_Json_pretty(x_416, x_418);
x_420 = lean_string_append(x_417, x_419);
lean_dec(x_419);
x_421 = lean_mk_string_unchecked("'", 1, 1);
x_422 = lean_string_append(x_420, x_421);
lean_dec(x_421);
x_423 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_423, 0, x_422);
lean_inc(x_31);
lean_inc(x_28);
x_424 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_423);
lean_inc(x_412);
x_425 = lean_apply_1(x_424, x_412);
x_401 = x_412;
x_402 = x_413;
x_403 = x_415;
x_404 = x_414;
x_405 = x_425;
goto block_411;
}
block_471:
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_5, 4);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = lean_box(0);
x_375 = x_427;
x_376 = x_428;
x_377 = x_429;
x_378 = x_432;
x_379 = x_430;
goto block_400;
}
else
{
uint8_t x_433; 
x_433 = !lean_is_exclusive(x_431);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_431, 0);
switch (lean_obj_tag(x_434)) {
case 2:
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_unsigned_to_nat(0u);
x_439 = lean_nat_dec_eq(x_437, x_438);
lean_dec(x_437);
if (x_439 == 0)
{
lean_dec(x_436);
lean_free_object(x_431);
x_412 = x_430;
x_413 = x_427;
x_414 = x_428;
x_415 = x_429;
x_416 = x_434;
goto block_426;
}
else
{
uint8_t x_440; 
x_440 = !lean_is_exclusive(x_434);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_434, 0);
lean_dec(x_441);
lean_ctor_set_tag(x_434, 0);
lean_ctor_set(x_434, 0, x_436);
lean_inc(x_31);
lean_inc(x_28);
x_442 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_431);
lean_inc(x_430);
x_443 = lean_apply_1(x_442, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_443;
goto block_411;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_434);
x_444 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_444, 0, x_436);
lean_ctor_set(x_431, 0, x_444);
lean_inc(x_31);
lean_inc(x_28);
x_445 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_431);
lean_inc(x_430);
x_446 = lean_apply_1(x_445, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_446;
goto block_411;
}
}
}
case 3:
{
uint8_t x_447; 
x_447 = !lean_is_exclusive(x_434);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; 
lean_ctor_set_tag(x_434, 1);
lean_inc(x_31);
lean_inc(x_28);
x_448 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_431);
lean_inc(x_430);
x_449 = lean_apply_1(x_448, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_449;
goto block_411;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_450 = lean_ctor_get(x_434, 0);
lean_inc(x_450);
lean_dec(x_434);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_431, 0, x_451);
lean_inc(x_31);
lean_inc(x_28);
x_452 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_431);
lean_inc(x_430);
x_453 = lean_apply_1(x_452, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_453;
goto block_411;
}
}
default: 
{
lean_free_object(x_431);
x_412 = x_430;
x_413 = x_427;
x_414 = x_428;
x_415 = x_429;
x_416 = x_434;
goto block_426;
}
}
}
else
{
lean_object* x_454; 
x_454 = lean_ctor_get(x_431, 0);
lean_inc(x_454);
lean_dec(x_431);
switch (lean_obj_tag(x_454)) {
case 2:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_unsigned_to_nat(0u);
x_459 = lean_nat_dec_eq(x_457, x_458);
lean_dec(x_457);
if (x_459 == 0)
{
lean_dec(x_456);
x_412 = x_430;
x_413 = x_427;
x_414 = x_428;
x_415 = x_429;
x_416 = x_454;
goto block_426;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 x_460 = x_454;
} else {
 lean_dec_ref(x_454);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(0, 1, 0);
} else {
 x_461 = x_460;
 lean_ctor_set_tag(x_461, 0);
}
lean_ctor_set(x_461, 0, x_456);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
lean_inc(x_31);
lean_inc(x_28);
x_463 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_462);
lean_inc(x_430);
x_464 = lean_apply_1(x_463, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_464;
goto block_411;
}
}
case 3:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_465 = lean_ctor_get(x_454, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 x_466 = x_454;
} else {
 lean_dec_ref(x_454);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 1, 0);
} else {
 x_467 = x_466;
 lean_ctor_set_tag(x_467, 1);
}
lean_ctor_set(x_467, 0, x_465);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_467);
lean_inc(x_31);
lean_inc(x_28);
x_469 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_468);
lean_inc(x_430);
x_470 = lean_apply_1(x_469, x_430);
x_401 = x_430;
x_402 = x_427;
x_403 = x_429;
x_404 = x_428;
x_405 = x_470;
goto block_411;
}
default: 
{
x_412 = x_430;
x_413 = x_427;
x_414 = x_428;
x_415 = x_429;
x_416 = x_454;
goto block_426;
}
}
}
}
}
block_495:
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_5, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; 
x_476 = lean_box(0);
x_427 = x_473;
x_428 = x_472;
x_429 = x_476;
x_430 = x_474;
goto block_471;
}
else
{
uint8_t x_477; 
x_477 = !lean_is_exclusive(x_475);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_478 = lean_ctor_get(x_475, 0);
x_479 = l_Lean_Json_getBool_x3f(x_478);
lean_dec(x_478);
lean_inc(x_31);
lean_inc(x_28);
x_480 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_479);
lean_inc(x_474);
x_481 = lean_apply_1(x_480, x_474);
if (lean_obj_tag(x_481) == 0)
{
uint8_t x_482; 
lean_free_object(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_482 = !lean_is_exclusive(x_481);
if (x_482 == 0)
{
return x_481;
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_484, 0, x_483);
return x_484;
}
}
else
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_481, 0);
lean_inc(x_485);
lean_dec(x_481);
lean_ctor_set(x_475, 0, x_485);
x_427 = x_473;
x_428 = x_472;
x_429 = x_475;
x_430 = x_474;
goto block_471;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_486 = lean_ctor_get(x_475, 0);
lean_inc(x_486);
lean_dec(x_475);
x_487 = l_Lean_Json_getBool_x3f(x_486);
lean_dec(x_486);
lean_inc(x_31);
lean_inc(x_28);
x_488 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_487);
lean_inc(x_474);
x_489 = lean_apply_1(x_488, x_474);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(0, 1, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_490);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_489, 0);
lean_inc(x_493);
lean_dec(x_489);
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_427 = x_473;
x_428 = x_472;
x_429 = x_494;
x_430 = x_474;
goto block_471;
}
}
}
}
block_504:
{
if (lean_obj_tag(x_498) == 0)
{
uint8_t x_499; 
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_498);
if (x_499 == 0)
{
return x_498;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_501, 0, x_500);
return x_501;
}
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_498, 0);
lean_inc(x_502);
lean_dec(x_498);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_472 = x_497;
x_473 = x_503;
x_474 = x_496;
goto block_495;
}
}
block_517:
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_508 = lean_mk_string_unchecked("unknown DiagnosticSeverity '", 28, 28);
x_509 = lean_unsigned_to_nat(80u);
x_510 = l_Lean_Json_pretty(x_505, x_509);
x_511 = lean_string_append(x_508, x_510);
lean_dec(x_510);
x_512 = lean_mk_string_unchecked("'", 1, 1);
x_513 = lean_string_append(x_511, x_512);
lean_dec(x_512);
x_514 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_514, 0, x_513);
lean_inc(x_31);
lean_inc(x_28);
x_515 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_514);
lean_inc(x_506);
x_516 = lean_apply_1(x_515, x_506);
x_496 = x_506;
x_497 = x_507;
x_498 = x_516;
goto block_504;
}
block_571:
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_5, 2);
lean_inc(x_520);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; 
x_521 = lean_box(0);
x_472 = x_518;
x_473 = x_521;
x_474 = x_519;
goto block_495;
}
else
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_520, 0);
lean_inc(x_522);
lean_dec(x_520);
lean_inc(x_522);
x_523 = l_Lean_Json_getNat_x3f(x_522);
if (lean_obj_tag(x_523) == 0)
{
lean_dec(x_523);
x_505 = x_522;
x_506 = x_519;
x_507 = x_518;
goto block_517;
}
else
{
uint8_t x_524; 
x_524 = !lean_is_exclusive(x_523);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_525 = lean_ctor_get(x_523, 0);
x_526 = lean_unsigned_to_nat(1u);
x_527 = lean_nat_dec_eq(x_525, x_526);
if (x_527 == 0)
{
lean_object* x_528; uint8_t x_529; 
x_528 = lean_unsigned_to_nat(2u);
x_529 = lean_nat_dec_eq(x_525, x_528);
if (x_529 == 0)
{
lean_object* x_530; uint8_t x_531; 
x_530 = lean_unsigned_to_nat(3u);
x_531 = lean_nat_dec_eq(x_525, x_530);
if (x_531 == 0)
{
lean_object* x_532; uint8_t x_533; 
x_532 = lean_unsigned_to_nat(4u);
x_533 = lean_nat_dec_eq(x_525, x_532);
lean_dec(x_525);
if (x_533 == 0)
{
lean_free_object(x_523);
x_505 = x_522;
x_506 = x_519;
x_507 = x_518;
goto block_517;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_522);
x_534 = lean_box(3);
lean_ctor_set(x_523, 0, x_534);
lean_inc(x_31);
lean_inc(x_28);
x_535 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_523);
lean_inc(x_519);
x_536 = lean_apply_1(x_535, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_536;
goto block_504;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_525);
lean_dec(x_522);
x_537 = lean_box(2);
lean_ctor_set(x_523, 0, x_537);
lean_inc(x_31);
lean_inc(x_28);
x_538 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_523);
lean_inc(x_519);
x_539 = lean_apply_1(x_538, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_539;
goto block_504;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_525);
lean_dec(x_522);
x_540 = lean_box(1);
lean_ctor_set(x_523, 0, x_540);
lean_inc(x_31);
lean_inc(x_28);
x_541 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_523);
lean_inc(x_519);
x_542 = lean_apply_1(x_541, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_542;
goto block_504;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_525);
lean_dec(x_522);
x_543 = lean_box(0);
lean_ctor_set(x_523, 0, x_543);
lean_inc(x_31);
lean_inc(x_28);
x_544 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_523);
lean_inc(x_519);
x_545 = lean_apply_1(x_544, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_545;
goto block_504;
}
}
else
{
lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_546 = lean_ctor_get(x_523, 0);
lean_inc(x_546);
lean_dec(x_523);
x_547 = lean_unsigned_to_nat(1u);
x_548 = lean_nat_dec_eq(x_546, x_547);
if (x_548 == 0)
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_unsigned_to_nat(2u);
x_550 = lean_nat_dec_eq(x_546, x_549);
if (x_550 == 0)
{
lean_object* x_551; uint8_t x_552; 
x_551 = lean_unsigned_to_nat(3u);
x_552 = lean_nat_dec_eq(x_546, x_551);
if (x_552 == 0)
{
lean_object* x_553; uint8_t x_554; 
x_553 = lean_unsigned_to_nat(4u);
x_554 = lean_nat_dec_eq(x_546, x_553);
lean_dec(x_546);
if (x_554 == 0)
{
x_505 = x_522;
x_506 = x_519;
x_507 = x_518;
goto block_517;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_522);
x_555 = lean_box(3);
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_555);
lean_inc(x_31);
lean_inc(x_28);
x_557 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_556);
lean_inc(x_519);
x_558 = lean_apply_1(x_557, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_558;
goto block_504;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_546);
lean_dec(x_522);
x_559 = lean_box(2);
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_559);
lean_inc(x_31);
lean_inc(x_28);
x_561 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_560);
lean_inc(x_519);
x_562 = lean_apply_1(x_561, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_562;
goto block_504;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_546);
lean_dec(x_522);
x_563 = lean_box(1);
x_564 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_564, 0, x_563);
lean_inc(x_31);
lean_inc(x_28);
x_565 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_564);
lean_inc(x_519);
x_566 = lean_apply_1(x_565, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_566;
goto block_504;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_546);
lean_dec(x_522);
x_567 = lean_box(0);
x_568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_568, 0, x_567);
lean_inc(x_31);
lean_inc(x_28);
x_569 = l_MonadExcept_ofExcept(lean_box(0), lean_box(0), lean_box(0), x_28, x_31, x_568);
lean_inc(x_519);
x_570 = lean_apply_1(x_569, x_519);
x_496 = x_519;
x_497 = x_518;
x_498 = x_570;
goto block_504;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__3____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__5____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853_), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Widget_TaggedText_stripTags___redArg(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Widget_TaggedText_stripTags___redArg(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_Widget_InteractiveGoal_pretty(x_10);
x_12 = lean_unsigned_to_nat(120u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_format_pretty(x_11, x_12, x_13, x_13);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Widget_InteractiveGoal_pretty(x_15);
x_17 = lean_unsigned_to_nat(120u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_format_pretty(x_16, x_17, x_18, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("(trace)", 7, 7);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed), 2, 0);
x_3 = l_Lean_Widget_TaggedText_rewrite___redArg(x_2, x_1);
x_4 = l_Lean_Widget_TaggedText_stripTags___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(x_8);
x_10 = lean_ctor_get(x_1, 7);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 8);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 9);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 10);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_5);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set(x_14, 5, x_7);
lean_ctor_set(x_14, 6, x_9);
lean_ctor_set(x_14, 7, x_10);
lean_ctor_set(x_14, 8, x_11);
lean_ctor_set(x_14, 9, x_12);
lean_ctor_set(x_14, 10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Array_empty(lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_push(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(4);
x_5 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_7, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_1);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = l_Array_empty(lean_box(0));
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_mk_string_unchecked("_diag", 5, 5);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 4, x_9);
lean_ctor_set(x_15, 5, x_10);
lean_ctor_set(x_15, 6, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_28; 
x_4 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_4, x_2);
if (x_28 == 0)
{
x_5 = x_28;
goto block_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
x_31 = l_Subarray_size___redArg(x_3);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_5 = x_32;
goto block_27;
}
block_27:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_ofSubarray___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; double x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = l_Array_ofSubarray___redArg(x_3);
x_8 = l_Subarray_size___redArg(x_3);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_7);
x_9 = l_Array_toSubarray___redArg(x_7, x_2, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(x_1, x_2, x_9);
lean_dec(x_9);
lean_inc(x_2);
x_11 = l_Array_toSubarray___redArg(x_7, x_4, x_2);
x_12 = l_Array_ofSubarray___redArg(x_11);
lean_dec(x_11);
x_13 = lean_float_of_nat(x_4);
x_14 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_13);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_5);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_nat_sub(x_8, x_2);
lean_dec(x_2);
lean_dec(x_8);
x_18 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked(" more entries...", 16, 16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_10);
x_26 = lean_array_push(x_12, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
x_11 = lean_apply_3(x_1, x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_17, x_3, x_14);
x_3 = x_20;
x_4 = x_21;
x_5 = x_15;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_17; 
lean_inc(x_2);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_7);
x_10 = x_17;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
lean_inc(x_2);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_10 = x_20;
goto block_16;
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 3)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_129; lean_object* x_130; lean_object* x_131; double x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_349 = l_Lean_Widget_instImpl____x40_Lean_Widget_Basic___hyg_28_;
if (lean_obj_tag(x_2) == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_1);
x_373 = lean_ctor_get(x_3, 0);
lean_inc(x_373);
lean_dec(x_3);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec(x_373);
x_375 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(x_374, x_4, x_5);
return x_375;
}
case 1:
{
uint8_t x_376; 
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_3);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_377 = lean_ctor_get(x_3, 0);
x_378 = lean_mk_string_unchecked("goal ", 5, 5);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_378);
x_379 = l_Lean_Expr_mvar___override(x_377);
x_380 = lean_expr_dbg_to_string(x_379);
lean_dec(x_379);
x_381 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_381, 0, x_380);
x_382 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_382, 0, x_3);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_4);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_5);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_385 = lean_ctor_get(x_3, 0);
lean_inc(x_385);
lean_dec(x_3);
x_386 = lean_mk_string_unchecked("goal ", 5, 5);
x_387 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_387, 0, x_386);
x_388 = l_Lean_Expr_mvar___override(x_385);
x_389 = lean_expr_dbg_to_string(x_388);
lean_dec(x_388);
x_390 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_390, 0, x_389);
x_391 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_391, 0, x_387);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_4);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_5);
return x_393;
}
}
case 2:
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_3, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_3, 1);
lean_inc(x_395);
lean_dec(x_3);
x_212 = x_2;
x_213 = x_394;
x_214 = x_395;
x_215 = x_4;
x_216 = x_5;
goto block_273;
}
case 3:
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_3, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_3, 1);
lean_inc(x_397);
lean_dec(x_3);
x_274 = x_396;
x_275 = x_397;
x_276 = x_4;
x_277 = x_5;
goto block_280;
}
case 4:
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_1);
x_398 = lean_ctor_get(x_3, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_3, 1);
lean_inc(x_399);
lean_dec(x_3);
x_1 = x_398;
x_3 = x_399;
goto _start;
}
case 5:
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_3, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_3, 1);
lean_inc(x_402);
lean_dec(x_3);
x_6 = x_2;
x_7 = x_401;
x_8 = x_402;
x_9 = x_4;
x_10 = x_5;
goto block_32;
}
case 6:
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_3, 0);
lean_inc(x_403);
lean_dec(x_3);
x_320 = x_2;
x_321 = x_403;
x_322 = x_4;
x_323 = x_5;
goto block_348;
}
case 7:
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_3, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_3, 1);
lean_inc(x_405);
lean_dec(x_3);
x_281 = x_2;
x_282 = x_404;
x_283 = x_405;
x_284 = x_4;
x_285 = x_5;
goto block_319;
}
case 8:
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_3, 1);
lean_inc(x_406);
lean_dec(x_3);
x_3 = x_406;
goto _start;
}
case 9:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_3, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_3, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_3, 2);
lean_inc(x_410);
lean_dec(x_3);
x_153 = x_2;
x_154 = x_408;
x_155 = x_409;
x_156 = x_410;
x_157 = x_4;
x_158 = x_5;
goto block_211;
}
default: 
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_3, 0);
lean_inc(x_411);
lean_dec(x_3);
x_412 = lean_box(0);
x_350 = x_2;
x_351 = x_4;
x_352 = x_411;
x_353 = x_5;
x_354 = x_412;
goto block_372;
}
}
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_413 = lean_ctor_get(x_3, 0);
lean_inc(x_413);
lean_dec(x_3);
x_414 = lean_ctor_get(x_2, 0);
lean_inc(x_414);
lean_dec(x_2);
x_415 = !lean_is_exclusive(x_413);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_416 = lean_ctor_get(x_413, 0);
x_417 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(x_1, x_414);
lean_dec(x_414);
lean_dec(x_1);
lean_ctor_set(x_413, 0, x_417);
x_418 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_413, x_4, x_5);
x_419 = !lean_is_exclusive(x_418);
if (x_419 == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_ctor_get(x_418, 0);
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_420, 0);
x_423 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_416);
lean_ctor_set(x_420, 0, x_423);
return x_418;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_424 = lean_ctor_get(x_420, 0);
x_425 = lean_ctor_get(x_420, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_420);
x_426 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_416);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
lean_ctor_set(x_418, 0, x_427);
return x_418;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_428 = lean_ctor_get(x_418, 0);
x_429 = lean_ctor_get(x_418, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_418);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_432 = x_428;
} else {
 lean_dec_ref(x_428);
 x_432 = lean_box(0);
}
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_416);
if (lean_is_scalar(x_432)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_432;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_431);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_429);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_436 = lean_ctor_get(x_413, 0);
x_437 = lean_ctor_get(x_413, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_413);
x_438 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(x_1, x_414);
lean_dec(x_414);
lean_dec(x_1);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
x_440 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_439, x_4, x_5);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_441, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_446 = x_441;
} else {
 lean_dec_ref(x_441);
 x_446 = lean_box(0);
}
x_447 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_436);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
if (lean_is_scalar(x_443)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_443;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_442);
return x_449;
}
}
case 1:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; 
x_450 = lean_ctor_get(x_2, 0);
lean_inc(x_450);
lean_dec(x_2);
x_451 = lean_ctor_get(x_3, 0);
lean_inc(x_451);
lean_dec(x_3);
x_452 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(x_1, x_450);
lean_dec(x_1);
x_453 = lean_ctor_get(x_450, 2);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set(x_454, 2, x_451);
x_455 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_454, x_4, x_5);
x_456 = !lean_is_exclusive(x_455);
if (x_456 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_ctor_get(x_455, 0);
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = lean_box(0);
x_461 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
lean_ctor_set(x_457, 0, x_461);
return x_455;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_ctor_get(x_457, 0);
x_463 = lean_ctor_get(x_457, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_457);
x_464 = lean_box(0);
x_465 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_464);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_463);
lean_ctor_set(x_455, 0, x_466);
return x_455;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_467 = lean_ctor_get(x_455, 0);
x_468 = lean_ctor_get(x_455, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_455);
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_471 = x_467;
} else {
 lean_dec_ref(x_467);
 x_471 = lean_box(0);
}
x_472 = lean_box(0);
x_473 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_473, 0, x_469);
lean_ctor_set(x_473, 1, x_472);
if (lean_is_scalar(x_471)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_471;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_470);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_468);
return x_475;
}
}
case 2:
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_ctor_get(x_3, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_3, 1);
lean_inc(x_477);
lean_dec(x_3);
x_212 = x_2;
x_213 = x_476;
x_214 = x_477;
x_215 = x_4;
x_216 = x_5;
goto block_273;
}
case 3:
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_2);
x_478 = lean_ctor_get(x_3, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_3, 1);
lean_inc(x_479);
lean_dec(x_3);
x_274 = x_478;
x_275 = x_479;
x_276 = x_4;
x_277 = x_5;
goto block_280;
}
case 4:
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_1);
x_480 = lean_ctor_get(x_3, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_3, 1);
lean_inc(x_481);
lean_dec(x_3);
x_1 = x_480;
x_3 = x_481;
goto _start;
}
case 5:
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_3, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_3, 1);
lean_inc(x_484);
lean_dec(x_3);
x_6 = x_2;
x_7 = x_483;
x_8 = x_484;
x_9 = x_4;
x_10 = x_5;
goto block_32;
}
case 6:
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_3, 0);
lean_inc(x_485);
lean_dec(x_3);
x_320 = x_2;
x_321 = x_485;
x_322 = x_4;
x_323 = x_5;
goto block_348;
}
case 7:
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_3, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_3, 1);
lean_inc(x_487);
lean_dec(x_3);
x_281 = x_2;
x_282 = x_486;
x_283 = x_487;
x_284 = x_4;
x_285 = x_5;
goto block_319;
}
case 8:
{
lean_object* x_488; 
x_488 = lean_ctor_get(x_3, 1);
lean_inc(x_488);
lean_dec(x_3);
x_3 = x_488;
goto _start;
}
case 9:
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_3, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_3, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_3, 2);
lean_inc(x_492);
lean_dec(x_3);
x_153 = x_2;
x_154 = x_490;
x_155 = x_491;
x_156 = x_492;
x_157 = x_4;
x_158 = x_5;
goto block_211;
}
default: 
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_493 = lean_ctor_get(x_2, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_3, 0);
lean_inc(x_494);
lean_dec(x_3);
x_495 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(x_1, x_493);
lean_dec(x_493);
x_496 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_496, 0, x_495);
x_350 = x_2;
x_351 = x_4;
x_352 = x_494;
x_353 = x_5;
x_354 = x_496;
goto block_372;
}
}
}
block_32:
{
lean_object* x_11; 
x_11 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_nat_to_int(x_7);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_13, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_nat_to_int(x_7);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = lean_nat_to_int(x_7);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
lean_dec(x_7);
return x_11;
}
}
block_62:
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get_uint8(x_33, sizeof(void*)*2 + 16);
lean_dec(x_33);
x_40 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
x_41 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_40, x_37, x_38);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_43, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_41, 0, x_52);
return x_41;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
}
block_75:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_array_get_size(x_69);
x_72 = l_Array_toSubarray___redArg(x_69, x_66, x_71);
lean_inc(x_65);
x_73 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(x_65, x_70, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_33 = x_64;
x_34 = x_65;
x_35 = x_68;
x_36 = x_74;
x_37 = x_67;
x_38 = x_63;
goto block_62;
}
block_85:
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_MessageData_maxTraceChildren;
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_63 = x_76;
x_64 = x_77;
x_65 = x_79;
x_66 = x_78;
x_67 = x_80;
x_68 = x_81;
x_69 = x_82;
x_70 = x_84;
goto block_75;
}
block_117:
{
if (x_93 == 0)
{
lean_object* x_94; size_t x_95; lean_object* x_96; size_t x_97; lean_object* x_98; 
x_94 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go), 5, 2);
lean_closure_set(x_94, 0, x_1);
lean_closure_set(x_94, 1, x_91);
x_95 = lean_array_size(x_89);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_usize_of_nat(x_96);
x_98 = l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(x_94, x_95, x_97, x_89, x_90, x_86);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_33 = x_87;
x_34 = x_88;
x_35 = x_92;
x_36 = x_103;
x_37 = x_102;
x_38 = x_100;
goto block_62;
}
else
{
uint8_t x_104; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
x_104 = !lean_is_exclusive(x_98);
if (x_104 == 0)
{
return x_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_98, 0);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_98);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
size_t x_108; lean_object* x_109; size_t x_110; lean_object* x_111; 
x_108 = lean_array_size(x_89);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_usize_of_nat(x_109);
x_111 = l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(x_91, x_1, x_108, x_110, x_89);
if (lean_obj_tag(x_91) == 0)
{
x_76 = x_86;
x_77 = x_87;
x_78 = x_109;
x_79 = x_88;
x_80 = x_90;
x_81 = x_92;
x_82 = x_111;
goto block_85;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
lean_dec(x_91);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_MessageData_maxTraceChildren;
x_115 = l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(x_113, x_114);
lean_dec(x_113);
if (lean_obj_tag(x_115) == 0)
{
x_76 = x_86;
x_77 = x_87;
x_78 = x_109;
x_79 = x_88;
x_80 = x_90;
x_81 = x_92;
x_82 = x_111;
goto block_85;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
x_63 = x_86;
x_64 = x_87;
x_65 = x_88;
x_66 = x_109;
x_67 = x_90;
x_68 = x_92;
x_69 = x_111;
x_70 = x_116;
goto block_75;
}
}
}
}
block_128:
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_119, sizeof(void*)*2 + 16);
if (x_126 == 0)
{
x_86 = x_125;
x_87 = x_119;
x_88 = x_120;
x_89 = x_121;
x_90 = x_124;
x_91 = x_122;
x_92 = x_123;
x_93 = x_126;
goto block_117;
}
else
{
uint8_t x_127; 
x_127 = l_Array_isEmpty___redArg(x_121);
if (x_127 == 0)
{
x_86 = x_125;
x_87 = x_119;
x_88 = x_120;
x_89 = x_121;
x_90 = x_124;
x_91 = x_122;
x_92 = x_123;
x_93 = x_126;
goto block_117;
}
else
{
x_86 = x_125;
x_87 = x_119;
x_88 = x_120;
x_89 = x_121;
x_90 = x_124;
x_91 = x_122;
x_92 = x_123;
x_93 = x_118;
goto block_117;
}
}
}
block_152:
{
lean_object* x_138; lean_object* x_139; double x_140; double x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_138 = lean_mk_string_unchecked("[", 1, 1);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_ctor_get_float(x_134, sizeof(void*)*2 + 8);
x_141 = lean_float_sub(x_140, x_132);
x_142 = lean_float_to_string(x_141);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("] ", 2, 2);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_133);
x_149 = lean_mk_string_unchecked("", 0, 0);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_118 = x_129;
x_119 = x_134;
x_120 = x_135;
x_121 = x_136;
x_122 = x_137;
x_123 = x_151;
x_124 = x_131;
x_125 = x_130;
goto block_128;
}
block_211:
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
x_160 = l_Lean_Name_isAnonymous(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_inc(x_153);
lean_inc(x_1);
x_161 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_153, x_155, x_157, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = !lean_is_exclusive(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; double x_169; lean_object* x_170; double x_171; uint8_t x_172; 
x_165 = lean_ctor_get(x_162, 0);
x_166 = lean_ctor_get(x_162, 1);
x_167 = lean_unsigned_to_nat(4u);
x_168 = lean_nat_to_int(x_167);
lean_ctor_set_tag(x_162, 4);
lean_ctor_set(x_162, 1, x_165);
lean_ctor_set(x_162, 0, x_168);
x_169 = lean_ctor_get_float(x_154, sizeof(void*)*2);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_float_of_nat(x_170);
x_172 = lean_float_beq(x_169, x_171);
if (x_172 == 0)
{
x_129 = x_160;
x_130 = x_163;
x_131 = x_166;
x_132 = x_169;
x_133 = x_162;
x_134 = x_154;
x_135 = x_159;
x_136 = x_156;
x_137 = x_153;
goto block_152;
}
else
{
if (x_160 == 0)
{
x_118 = x_160;
x_119 = x_154;
x_120 = x_159;
x_121 = x_156;
x_122 = x_153;
x_123 = x_162;
x_124 = x_166;
x_125 = x_163;
goto block_128;
}
else
{
x_129 = x_160;
x_130 = x_163;
x_131 = x_166;
x_132 = x_169;
x_133 = x_162;
x_134 = x_154;
x_135 = x_159;
x_136 = x_156;
x_137 = x_153;
goto block_152;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; double x_178; lean_object* x_179; double x_180; uint8_t x_181; 
x_173 = lean_ctor_get(x_162, 0);
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_162);
x_175 = lean_unsigned_to_nat(4u);
x_176 = lean_nat_to_int(x_175);
x_177 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
x_178 = lean_ctor_get_float(x_154, sizeof(void*)*2);
x_179 = lean_unsigned_to_nat(0u);
x_180 = lean_float_of_nat(x_179);
x_181 = lean_float_beq(x_178, x_180);
if (x_181 == 0)
{
x_129 = x_160;
x_130 = x_163;
x_131 = x_174;
x_132 = x_178;
x_133 = x_177;
x_134 = x_154;
x_135 = x_159;
x_136 = x_156;
x_137 = x_153;
goto block_152;
}
else
{
if (x_160 == 0)
{
x_118 = x_160;
x_119 = x_154;
x_120 = x_159;
x_121 = x_156;
x_122 = x_153;
x_123 = x_177;
x_124 = x_174;
x_125 = x_163;
goto block_128;
}
else
{
x_129 = x_160;
x_130 = x_163;
x_131 = x_174;
x_132 = x_178;
x_133 = x_177;
x_134 = x_154;
x_135 = x_159;
x_136 = x_156;
x_137 = x_153;
goto block_152;
}
}
}
}
else
{
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_1);
return x_161;
}
}
else
{
lean_object* x_182; size_t x_183; lean_object* x_184; size_t x_185; lean_object* x_186; 
lean_dec(x_159);
lean_dec(x_155);
lean_dec(x_154);
x_182 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go), 5, 2);
lean_closure_set(x_182, 0, x_1);
lean_closure_set(x_182, 1, x_153);
x_183 = lean_array_size(x_156);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_usize_of_nat(x_184);
x_186 = l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(x_182, x_183, x_185, x_156, x_157, x_158);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_array_to_list(x_190);
x_192 = l_Std_Format_join(x_191);
lean_ctor_set(x_188, 0, x_192);
return x_186;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_188);
x_195 = lean_array_to_list(x_193);
x_196 = l_Std_Format_join(x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_186, 0, x_197);
return x_186;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_ctor_get(x_186, 0);
x_199 = lean_ctor_get(x_186, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_186);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
 x_202 = lean_box(0);
}
x_203 = lean_array_to_list(x_200);
x_204 = l_Std_Format_join(x_203);
if (lean_is_scalar(x_202)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_202;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_201);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_199);
return x_206;
}
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_186);
if (x_207 == 0)
{
return x_186;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_186, 0);
x_209 = lean_ctor_get(x_186, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_186);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
block_273:
{
lean_object* x_217; 
x_217 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_212, x_214, x_215, x_216);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_217, 1);
x_222 = lean_ctor_get(x_219, 0);
x_223 = lean_ctor_get(x_219, 1);
lean_ctor_set_tag(x_219, 2);
lean_ctor_set(x_219, 1, x_222);
lean_ctor_set(x_219, 0, x_213);
x_224 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_219, x_223, x_221);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_box(0);
lean_ctor_set_tag(x_217, 7);
lean_ctor_set(x_217, 1, x_229);
lean_ctor_set(x_217, 0, x_228);
lean_ctor_set(x_226, 0, x_217);
return x_224;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_226, 0);
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_226);
x_232 = lean_box(0);
lean_ctor_set_tag(x_217, 7);
lean_ctor_set(x_217, 1, x_232);
lean_ctor_set(x_217, 0, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_217);
lean_ctor_set(x_233, 1, x_231);
lean_ctor_set(x_224, 0, x_233);
return x_224;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_224, 0);
x_235 = lean_ctor_get(x_224, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_224);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_238 = x_234;
} else {
 lean_dec_ref(x_234);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
lean_ctor_set_tag(x_217, 7);
lean_ctor_set(x_217, 1, x_239);
lean_ctor_set(x_217, 0, x_236);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_217);
lean_ctor_set(x_240, 1, x_237);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_235);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_242 = lean_ctor_get(x_217, 1);
x_243 = lean_ctor_get(x_219, 0);
x_244 = lean_ctor_get(x_219, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_219);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_213);
lean_ctor_set(x_245, 1, x_243);
x_246 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_245, x_244, x_242);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_252 = x_247;
} else {
 lean_dec_ref(x_247);
 x_252 = lean_box(0);
}
x_253 = lean_box(0);
lean_ctor_set_tag(x_217, 7);
lean_ctor_set(x_217, 1, x_253);
lean_ctor_set(x_217, 0, x_250);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_217);
lean_ctor_set(x_254, 1, x_251);
if (lean_is_scalar(x_249)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_249;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_248);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_256 = lean_ctor_get(x_217, 0);
x_257 = lean_ctor_get(x_217, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_217);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_260 = x_256;
} else {
 lean_dec_ref(x_256);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(2, 2, 0);
} else {
 x_261 = x_260;
 lean_ctor_set_tag(x_261, 2);
}
lean_ctor_set(x_261, 0, x_213);
lean_ctor_set(x_261, 1, x_258);
x_262 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(x_261, x_259, x_257);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_263, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_268 = x_263;
} else {
 lean_dec_ref(x_263);
 x_268 = lean_box(0);
}
x_269 = lean_box(0);
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_269);
if (lean_is_scalar(x_268)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_268;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_267);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
return x_272;
}
}
else
{
lean_dec(x_213);
return x_217;
}
}
block_280:
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_274);
x_2 = x_278;
x_3 = x_275;
x_4 = x_276;
x_5 = x_277;
goto _start;
}
block_319:
{
lean_object* x_286; 
lean_inc(x_281);
lean_inc(x_1);
x_286 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_281, x_282, x_284, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = !lean_is_exclusive(x_287);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_287, 0);
x_291 = lean_ctor_get(x_287, 1);
x_292 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_281, x_283, x_291, x_288);
if (lean_obj_tag(x_292) == 0)
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = lean_ctor_get(x_292, 0);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_294, 0);
lean_ctor_set_tag(x_287, 5);
lean_ctor_set(x_287, 1, x_296);
lean_ctor_set(x_294, 0, x_287);
return x_292;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_294, 0);
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_294);
lean_ctor_set_tag(x_287, 5);
lean_ctor_set(x_287, 1, x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_287);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set(x_292, 0, x_299);
return x_292;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_292, 0);
x_301 = lean_ctor_get(x_292, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_292);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_304 = x_300;
} else {
 lean_dec_ref(x_300);
 x_304 = lean_box(0);
}
lean_ctor_set_tag(x_287, 5);
lean_ctor_set(x_287, 1, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_287);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_301);
return x_306;
}
}
else
{
lean_free_object(x_287);
lean_dec(x_290);
return x_292;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_287, 0);
x_308 = lean_ctor_get(x_287, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_287);
x_309 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_281, x_283, x_308, x_288);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_310, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_310, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_315 = x_310;
} else {
 lean_dec_ref(x_310);
 x_315 = lean_box(0);
}
x_316 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_316, 0, x_307);
lean_ctor_set(x_316, 1, x_313);
if (lean_is_scalar(x_315)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_315;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_314);
if (lean_is_scalar(x_312)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_312;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_311);
return x_318;
}
else
{
lean_dec(x_307);
return x_309;
}
}
}
else
{
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_1);
return x_286;
}
}
block_348:
{
lean_object* x_324; 
x_324 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_1, x_320, x_321, x_322, x_323);
if (lean_obj_tag(x_324) == 0)
{
uint8_t x_325; 
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_324, 0);
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = lean_ctor_get(x_326, 0);
x_329 = lean_box(0);
x_330 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_330, 0, x_328);
x_331 = lean_unbox(x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*1, x_331);
lean_ctor_set(x_326, 0, x_330);
return x_324;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_332 = lean_ctor_get(x_326, 0);
x_333 = lean_ctor_get(x_326, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_326);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_335, 0, x_332);
x_336 = lean_unbox(x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*1, x_336);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_333);
lean_ctor_set(x_324, 0, x_337);
return x_324;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; 
x_338 = lean_ctor_get(x_324, 0);
x_339 = lean_ctor_get(x_324, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_324);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_342 = x_338;
} else {
 lean_dec_ref(x_338);
 x_342 = lean_box(0);
}
x_343 = lean_box(0);
x_344 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_344, 0, x_340);
x_345 = lean_unbox(x_343);
lean_ctor_set_uint8(x_344, sizeof(void*)*1, x_345);
if (lean_is_scalar(x_342)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_342;
}
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_341);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_339);
return x_347;
}
}
else
{
return x_324;
}
}
block_372:
{
lean_object* x_355; uint8_t x_356; 
x_355 = lean_apply_2(x_352, x_354, x_353);
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_355, 0);
x_358 = lean_ctor_get(x_355, 1);
x_359 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_357, x_349);
lean_dec(x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_1);
x_360 = lean_mk_string_unchecked("MessageData.ofLazy: expected MessageData in Dynamic", 51, 51);
x_361 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set_tag(x_355, 1);
lean_ctor_set(x_355, 0, x_361);
return x_355;
}
else
{
lean_object* x_362; 
lean_free_object(x_355);
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
lean_dec(x_359);
x_2 = x_350;
x_3 = x_362;
x_4 = x_351;
x_5 = x_358;
goto _start;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_355, 0);
x_365 = lean_ctor_get(x_355, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_355);
x_366 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_364, x_349);
lean_dec(x_364);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_1);
x_367 = lean_mk_string_unchecked("MessageData.ofLazy: expected MessageData in Dynamic", 51, 51);
x_368 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_365);
return x_369;
}
else
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_366, 0);
lean_inc(x_370);
lean_dec(x_366);
x_2 = x_350;
x_3 = x_370;
x_4 = x_351;
x_5 = x_365;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at_____private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(x_5, x_6, x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_1, x_10);
lean_inc(x_2);
x_12 = l_Lean_Widget_msgToInteractive_fmtToTT(x_2, x_9, x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_5, x_4, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_array_uset(x_16, x_4, x_13);
x_4 = x_19;
x_5 = x_20;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_6, x_2, x_7);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
x_9 = l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(x_1, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
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
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(x_1, x_7, x_9, x_6, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_array_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(x_1, x_21, x_23, x_20, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_apply_3(x_1, x_34, x_35, x_3);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Widget_goalToInteractive(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = lean_array_get(x_1, x_2, x_7);
lean_dec(x_7);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Widget_tagCodeInfos_go(x_12, x_13, x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_15);
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = l_Lean_Widget_tagCodeInfos_go(x_19, x_20, x_5);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
if (lean_is_scalar(x_9)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_9;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_10, 2);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_27, x_28, x_30, x_6);
return x_31;
}
case 2:
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
x_35 = l_Lean_Widget_msgToInteractive_fmtToTT(x_2, x_34, x_8, x_6);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_10, 1, x_37);
x_38 = lean_mk_string_unchecked("", 0, 0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_9)) {
 x_40 = lean_alloc_ctor(2, 2, 0);
} else {
 x_40 = x_9;
 lean_ctor_set_tag(x_40, 2);
}
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_35, 0, x_40);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
lean_ctor_set(x_10, 1, x_41);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_9)) {
 x_45 = lean_alloc_ctor(2, 2, 0);
} else {
 x_45 = x_9;
 lean_ctor_set_tag(x_45, 2);
}
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_free_object(x_10);
lean_dec(x_33);
lean_dec(x_9);
return x_35;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_49 = l_Lean_Widget_msgToInteractive_fmtToTT(x_2, x_48, x_8, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_mk_string_unchecked("", 0, 0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_9)) {
 x_56 = lean_alloc_ctor(2, 2, 0);
} else {
 x_56 = x_9;
 lean_ctor_set_tag(x_56, 2);
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
else
{
lean_dec(x_47);
lean_dec(x_9);
return x_49;
}
}
}
case 3:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
x_58 = lean_ctor_get(x_10, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_61 = lean_ctor_get(x_10, 2);
lean_inc(x_61);
lean_dec(x_10);
x_62 = lean_nat_add(x_3, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
lean_object* x_81; size_t x_82; lean_object* x_83; size_t x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_61, 0);
x_82 = lean_array_size(x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_usize_of_nat(x_83);
lean_inc(x_2);
x_85 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0(x_62, x_2, x_82, x_84, x_81, x_6);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_86);
x_63 = x_61;
x_64 = x_87;
goto block_79;
}
else
{
uint8_t x_88; 
lean_free_object(x_61);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; size_t x_93; lean_object* x_94; size_t x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_61, 0);
lean_inc(x_92);
lean_dec(x_61);
x_93 = lean_array_size(x_92);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_usize_of_nat(x_94);
lean_inc(x_2);
x_96 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0(x_62, x_2, x_93, x_95, x_92, x_6);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_97);
x_63 = x_99;
x_64 = x_98;
goto block_79;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_102 = x_96;
} else {
 lean_dec_ref(x_96);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_61);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_61, 0);
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_nat_add(x_62, x_106);
x_108 = lean_array_size(x_105);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_usize_of_nat(x_109);
x_111 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1(x_108, x_110, x_105);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_61, 0, x_112);
x_63 = x_61;
x_64 = x_6;
goto block_79;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_61, 0);
lean_inc(x_113);
lean_dec(x_61);
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_nat_add(x_62, x_114);
x_116 = lean_array_size(x_113);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_usize_of_nat(x_117);
x_119 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1(x_116, x_118, x_113);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_63 = x_121;
x_64 = x_6;
goto block_79;
}
}
block_79:
{
lean_object* x_65; 
x_65 = l_Lean_Widget_msgToInteractive_fmtToTT(x_2, x_59, x_62, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_60);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_9)) {
 x_71 = lean_alloc_ctor(2, 2, 0);
} else {
 x_71 = x_9;
 lean_ctor_set_tag(x_71, 2);
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_72);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_60);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
if (lean_is_scalar(x_9)) {
 x_77 = lean_alloc_ctor(2, 2, 0);
} else {
 x_77 = x_9;
 lean_ctor_set_tag(x_77, 2);
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
}
else
{
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_3);
return x_65;
}
}
}
default: 
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_122 = l_Lean_Widget_TaggedText_stripTags___redArg(x_5);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_is_scalar(x_9)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_9;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_6);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Widget_instInhabitedEmbedFmt;
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractive_fmtToTT___lam__1), 6, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_unsigned_to_nat(120u);
x_8 = l_Lean_Widget_TaggedText_prettyTagged(x_2, x_3, x_7);
x_9 = l_Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(x_6, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Widget_msgToInteractive_fmtToTT_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Widget_TaggedText_rewriteM___at___Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Widget_msgToInteractive_fmtToTT___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Widget_TaggedText_stripTags___redArg(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_MessageData_format(x_1, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractive___lam__0___boxed), 2, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(120u);
x_12 = l_Lean_Widget_TaggedText_prettyTagged(x_8, x_10, x_11);
x_13 = l_Lean_Widget_TaggedText_rewrite___redArg(x_9, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractive___lam__0___boxed), 2, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(120u);
x_19 = l_Lean_Widget_TaggedText_prettyTagged(x_14, x_17, x_18);
x_20 = l_Lean_Widget_TaggedText_rewrite___redArg(x_16, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(x_1, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Widget_msgToInteractive_fmtToTT(x_26, x_25, x_3, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_msgToInteractive___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Widget_msgToInteractive(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("Tactic", 6, 6);
x_3 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_name_eq(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("goalsAccomplished", 17, 17);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_name_eq(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_110; lean_object* x_111; lean_object* x_114; lean_object* x_115; 
x_42 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed), 1, 0);
x_43 = lean_alloc_closure((void*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed), 1, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_inc(x_96);
x_97 = l_Lean_FileMap_leanPosToLspPos(x_1, x_96);
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_inc(x_96);
x_115 = x_96;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_114, 0);
lean_inc(x_129);
x_115 = x_129;
goto block_128;
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_6);
lean_ctor_set(x_18, 3, x_9);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_11);
lean_ctor_set(x_18, 6, x_13);
lean_ctor_set(x_18, 7, x_5);
lean_ctor_set(x_18, 8, x_10);
lean_ctor_set(x_18, 9, x_16);
lean_ctor_set(x_18, 10, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
block_41:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Widget_msgToInteractive(x_25, x_3, x_29, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_5 = x_21;
x_6 = x_22;
x_7 = x_23;
x_8 = x_32;
x_9 = x_24;
x_10 = x_28;
x_11 = x_26;
x_12 = x_27;
x_13 = x_31;
goto block_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_mk_string_unchecked("[error when printing message: ", 30, 30);
x_36 = lean_io_error_to_string(x_33);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked("]", 1, 1);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_5 = x_21;
x_6 = x_22;
x_7 = x_23;
x_8 = x_34;
x_9 = x_24;
x_10 = x_28;
x_11 = x_26;
x_12 = x_27;
x_13 = x_40;
goto block_20;
}
}
block_64:
{
uint8_t x_51; 
lean_inc(x_47);
x_51 = l_Lean_MessageData_hasTag(x_42, x_47);
if (x_51 == 0)
{
uint8_t x_52; 
lean_inc(x_47);
x_52 = l_Lean_MessageData_hasTag(x_43, x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_21 = x_50;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_49;
x_27 = x_48;
x_28 = x_53;
goto block_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_box(1);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_mk_empty_array_with_capacity(x_55);
x_57 = lean_array_push(x_56, x_54);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_21 = x_50;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_49;
x_27 = x_48;
x_28 = x_58;
goto block_41;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
x_59 = lean_box(0);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
x_62 = lean_array_push(x_61, x_59);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_21 = x_50;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_49;
x_27 = x_48;
x_28 = x_63;
goto block_41;
}
}
block_85:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_mk_string_unchecked("Lean 4", 6, 6);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_ctor_get(x_2, 4);
lean_inc(x_71);
lean_dec(x_2);
lean_inc(x_71);
x_72 = l_Lean_MessageData_isDeprecationWarning(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_inc(x_71);
x_73 = l_Lean_MessageData_isUnusedVariableWarning(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_box(0);
x_44 = x_65;
x_45 = x_66;
x_46 = x_68;
x_47 = x_71;
x_48 = x_67;
x_49 = x_70;
x_50 = x_74;
goto block_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_array_push(x_77, x_75);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_44 = x_65;
x_45 = x_66;
x_46 = x_68;
x_47 = x_71;
x_48 = x_67;
x_49 = x_70;
x_50 = x_79;
goto block_64;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_box(1);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_mk_empty_array_with_capacity(x_81);
x_83 = lean_array_push(x_82, x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_44 = x_65;
x_45 = x_66;
x_46 = x_68;
x_47 = x_71;
x_48 = x_67;
x_49 = x_70;
x_50 = x_84;
goto block_64;
}
}
block_95:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_65 = x_90;
x_66 = x_86;
x_67 = x_87;
x_68 = x_92;
goto block_85;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_box(x_91);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_65 = x_90;
x_66 = x_86;
x_67 = x_87;
x_68 = x_94;
goto block_85;
}
}
block_109:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_inc(x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
switch (x_102) {
case 0:
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_box(2);
x_104 = lean_unbox(x_103);
x_86 = x_100;
x_87 = x_101;
x_88 = x_104;
goto block_95;
}
case 1:
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_box(1);
x_106 = lean_unbox(x_105);
x_86 = x_100;
x_87 = x_101;
x_88 = x_106;
goto block_95;
}
default: 
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_box(0);
x_108 = lean_unbox(x_107);
x_86 = x_100;
x_87 = x_101;
x_88 = x_108;
goto block_95;
}
}
}
block_113:
{
lean_object* x_112; 
x_112 = l_Lean_FileMap_leanPosToLspPos(x_1, x_111);
x_98 = x_110;
x_99 = x_112;
goto block_109;
}
block_128:
{
lean_object* x_116; 
x_116 = l_Lean_FileMap_leanPosToLspPos(x_1, x_115);
if (lean_obj_tag(x_114) == 0)
{
lean_dec(x_96);
lean_inc(x_97);
x_98 = x_116;
x_99 = x_97;
goto block_109;
}
else
{
uint8_t x_117; 
x_117 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_ctor_get(x_96, 0);
lean_inc(x_119);
lean_dec(x_96);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_nat_dec_lt(x_119, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_dec(x_119);
x_110 = x_116;
x_111 = x_118;
goto block_113;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_118);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_119, x_122);
lean_dec(x_119);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_FileMap_leanPosToLspPos(x_1, x_125);
x_98 = x_116;
x_99 = x_126;
goto block_109;
}
}
else
{
lean_object* x_127; 
lean_dec(x_96);
x_127 = lean_ctor_get(x_114, 0);
lean_inc(x_127);
lean_dec(x_114);
x_110 = x_116;
x_111 = x_127;
goto block_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Widget_msgToInteractiveDiagnostic(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_Linter_UnusedVariables(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveGoal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_UnusedVariables(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveGoal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_207_ = _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_207_();
lean_mark_persistent(l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_207_);
l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_264_ = _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_264_();
lean_mark_persistent(l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_264_);
l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_ = _init_l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_();
lean_mark_persistent(l_Lean_Widget_instImpl____x40_Lean_Widget_InteractiveDiagnostic___hyg_548_);
l_Lean_Widget_instTypeNameLazyTraceChildren = _init_l_Lean_Widget_instTypeNameLazyTraceChildren();
lean_mark_persistent(l_Lean_Widget_instTypeNameLazyTraceChildren);
l_Lean_Widget_instInhabitedMsgEmbed = _init_l_Lean_Widget_instInhabitedMsgEmbed();
lean_mark_persistent(l_Lean_Widget_instInhabitedMsgEmbed);
l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1113_ = _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1113_();
lean_mark_persistent(l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1113_);
l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1279_ = _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1279_();
lean_mark_persistent(l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_1279_);
l_Lean_Widget_instRpcEncodableMsgEmbed = _init_l_Lean_Widget_instRpcEncodableMsgEmbed();
lean_mark_persistent(l_Lean_Widget_instRpcEncodableMsgEmbed);
l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2608_ = _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2608_();
lean_mark_persistent(l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2608_);
l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2696_ = _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2696_();
lean_mark_persistent(l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2696_);
l_Lean_Widget_instInhabitedEmbedFmt = _init_l_Lean_Widget_instInhabitedEmbedFmt();
lean_mark_persistent(l_Lean_Widget_instInhabitedEmbedFmt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
