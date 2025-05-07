// Lean compiler output
// Module: Lean.Server.Rpc.RequestHandling
// Imports: Lean.Data.Lsp.Extra Lean.Server.Requests Lean.Server.Rpc.Basic
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
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_builtinRpcProcedures;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(lean_object*);
lean_object* l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_33_(lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409_(lean_object*);
extern lean_object* l_instHashableString;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_2250_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__4(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_userRpcProcedures;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__1(uint64_t, uint64_t);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__0(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___lam__0(uint64_t, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRpcProcedure() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_instInhabitedRpcProcedure___lam__0___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = l_Lean_Server_instInhabitedRpcProcedure___lam__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_33_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Server", 6, 6);
x_5 = lean_mk_string_unchecked("userRpcProcedures", 17, 17);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = l_Lean_mkMapDeclarationExtension___redArg(x_6, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("_private", 8, 8);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("Rpc", 3, 3);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Name_num___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_7);
x_18 = l_Lean_Name_str___override(x_17, x_9);
x_19 = lean_mk_string_unchecked("RpcProcedure", 12, 12);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = l_Lean_Environment_evalConstCheck___redArg(x_1, x_2, x_20, x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_Snapshots_Snapshot_endPos(x_4);
x_6 = lean_nat_dec_le(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Server_userRpcProcedures;
x_8 = l_Lean_Server_Snapshots_Snapshot_env(x_4);
x_9 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_2, x_7, x_8, x_3, x_6);
if (lean_obj_tag(x_9) == 0)
{
return x_6;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = l_Lean_Server_userRpcProcedures;
x_12 = l_Lean_Server_Snapshots_Snapshot_env(x_8);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_12);
x_15 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_1, x_11, x_12, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_18, 2);
x_20 = l_List_head_x21(lean_box(0), x_4, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_17);
x_22 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(x_12, x_21, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(4);
x_25 = lean_mk_string_unchecked("Failed to evaluate RPC constant '", 33, 33);
x_26 = l_Lean_Name_toString(x_17, x_5, x_6);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("': ", 3, 3);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_23);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unbox(x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
else
{
lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_6);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_36 = lean_ctor_get(x_7, 2);
lean_inc(x_36);
lean_dec(x_7);
x_37 = lean_box_uint64(x_35);
x_38 = lean_apply_4(x_34, x_37, x_36, x_9, x_10);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint64(x_2);
x_7 = lean_apply_4(x_1, x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_task_get_own(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_task_get_own(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Server_builtinRpcProcedures;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_10 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 1, 0);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Command_instInhabitedScope;
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_FileMap_lspPosToUtf8Pos(x_18, x_20);
lean_dec(x_18);
lean_inc(x_8);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__2___boxed), 4, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_8);
x_23 = lean_box(2);
x_24 = lean_mk_string_unchecked("No RPC method '", 15, 15);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
lean_inc(x_13);
lean_inc(x_8);
x_27 = l_Lean_Name_toString(x_8, x_26, x_13);
x_28 = lean_string_append(x_24, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("' found", 7, 7);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unbox(x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
lean_inc(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__1___boxed), 3, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__3___boxed), 10, 7);
lean_closure_set(x_34, 0, x_14);
lean_closure_set(x_34, 1, x_8);
lean_closure_set(x_34, 2, x_31);
lean_closure_set(x_34, 3, x_15);
lean_closure_set(x_34, 4, x_25);
lean_closure_set(x_34, 5, x_13);
lean_closure_set(x_34, 6, x_1);
x_35 = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(x_11, x_22, x_33, x_34, x_2, x_12);
return x_35;
}
else
{
lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
lean_dec(x_9);
x_37 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_box_uint64(x_37);
x_40 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__4___boxed), 5, 3);
lean_closure_set(x_40, 0, x_36);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_38);
x_41 = l_Lean_Server_RequestM_asTask___redArg(x_40, x_2, x_7);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_handleRpcCall___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Server_handleRpcCall___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_handleRpcCall___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_handleRpcCall___lam__3(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Lean_Server_handleRpcCall___lam__4(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_2250_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(3);
x_6 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
x_7 = l_Lean_Json_compress(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\n", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_4);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unbox(x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(3);
x_16 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
x_17 = l_Lean_Json_compress(x_1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("\n", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_14);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unbox(x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__0(x_1);
x_4 = l_EIO_ofExcept(lean_box(0), lean_box(0), x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_5 = l_instBEqOfDecidableEq___redArg(x_4);
x_6 = l_instHashableString;
x_7 = lean_string_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_5, x_6, x_1, x_8, x_10, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__0(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_3(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_dec(x_2);
return x_9;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_initializing(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_mk_string_unchecked("Failed to register LSP request handler for '", 44, 44);
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("': only possible during initialization", 38, 38);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_mk_string_unchecked("Failed to register LSP request handler for '", 44, 44);
x_16 = lean_string_append(x_15, x_1);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("': only possible during initialization", 38, 38);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Server_requestHandlers;
x_23 = lean_st_ref_get(x_22, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_PersistentHashMap_contains___at___Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(x_25, x_1);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_free_object(x_23);
x_28 = lean_st_ref_take(x_22, x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0___boxed), 1, 0);
x_33 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__1), 1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__2), 5, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_32);
lean_ctor_set(x_28, 1, x_34);
lean_ctor_set(x_28, 0, x_33);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(x_30, x_1, x_28);
x_36 = lean_st_ref_set(x_22, x_35, x_31);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0___boxed), 1, 0);
x_44 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__1), 1, 0);
x_45 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__2), 5, 2);
lean_closure_set(x_45, 0, x_2);
lean_closure_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(x_41, x_1, x_46);
x_48 = lean_st_ref_set(x_22, x_47, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_53 = lean_mk_string_unchecked("Failed to register LSP request handler for '", 44, 44);
x_54 = lean_string_append(x_53, x_1);
lean_dec(x_1);
x_55 = lean_mk_string_unchecked("': already registered", 21, 21);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = l_Lean_PersistentHashMap_contains___at___Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(x_58, x_1);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_st_ref_take(x_22, x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0___boxed), 1, 0);
x_66 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__1), 1, 0);
x_67 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__2), 5, 2);
lean_closure_set(x_67, 0, x_2);
lean_closure_set(x_67, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_PersistentHashMap_insert___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__2___redArg(x_62, x_1, x_68);
x_70 = lean_st_ref_set(x_22, x_69, x_63);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_75 = lean_mk_string_unchecked("Failed to register LSP request handler for '", 44, 44);
x_76 = lean_string_append(x_75, x_1);
lean_dec(x_1);
x_77 = lean_mk_string_unchecked("': already registered", 21, 21);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_59);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("$/lean/rpc/call", 15, 15);
x_3 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall), 3, 0);
x_4 = l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_wrapRpcProcedure___redArg___lam__1(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint64_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_st_ref_take(x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_13, 0, lean_box(0));
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_apply_2(x_14, x_8, x_15);
x_17 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_13, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_set(x_1, x_19, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint64_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_box_uint64(x_7);
x_13 = l_Lean_RBNode_find(lean_box(0), x_1, lean_box(0), x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(9);
x_15 = lean_mk_string_unchecked("Outdated RPC session", 20, 20);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_st_ref_get(x_19, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_8);
x_26 = lean_apply_2(x_24, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(3);
x_29 = lean_mk_string_unchecked("Cannot decode params in RPC call '", 34, 34);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Name_toString(x_3, x_31, x_4);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("(", 1, 1);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_Json_compress(x_8);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(")'\n", 3, 3);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_27);
lean_dec(x_27);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_unbox(x_28);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
lean_inc(x_9);
x_44 = lean_apply_3(x_5, x_43, x_9, x_23);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(x_47, 0, x_19);
lean_closure_set(x_47, 1, x_6);
x_48 = l_Lean_Server_RequestM_mapTaskCheap___redArg(x_45, x_47, x_9, x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_8);
x_57 = lean_apply_2(x_55, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(3);
x_60 = lean_mk_string_unchecked("Cannot decode params in RPC call '", 34, 34);
x_61 = lean_box(1);
x_62 = lean_unbox(x_61);
x_63 = l_Lean_Name_toString(x_3, x_62, x_4);
x_64 = lean_string_append(x_60, x_63);
lean_dec(x_63);
x_65 = lean_mk_string_unchecked("(", 1, 1);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = l_Lean_Json_compress(x_8);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_69 = lean_mk_string_unchecked(")'\n", 3, 3);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_string_append(x_70, x_58);
lean_dec(x_58);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_unbox(x_59);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_54);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_57, 0);
lean_inc(x_75);
lean_dec(x_57);
lean_inc(x_9);
x_76 = lean_apply_3(x_5, x_75, x_9, x_54);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed), 5, 2);
lean_closure_set(x_79, 0, x_19);
lean_closure_set(x_79, 1, x_6);
x_80 = l_Lean_Server_RequestM_mapTaskCheap___redArg(x_77, x_79, x_9, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__1___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed), 10, 6);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_4);
lean_closure_set(x_7, 5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_wrapRpcProcedure___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_Server_wrapRpcProcedure___redArg___lam__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_wrapRpcProcedure___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; lean_object* x_12; 
x_11 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_12 = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_initializing(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 1, 0);
x_11 = lean_box(1);
x_12 = lean_mk_string_unchecked("Failed to register builtin RPC call handler for '", 49, 49);
x_13 = lean_unbox(x_11);
lean_inc(x_1);
x_14 = l_Lean_Name_toString(x_1, x_13, x_10);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("'", 1, 1);
x_17 = lean_unbox(x_8);
lean_dec(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked(": only possible during initialization", 37, 37);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_6);
x_22 = l_Lean_Server_builtinRpcProcedures;
x_23 = lean_st_ref_get(x_22, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Name_instBEq;
x_28 = l_Lean_instHashableName;
lean_inc(x_1);
x_29 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_27, x_28, x_25, x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_23);
lean_dec(x_16);
lean_dec(x_15);
x_30 = lean_st_ref_take(x_22, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_1);
x_33 = l_Lean_Server_wrapRpcProcedure___redArg(x_1, x_2, x_3, x_4);
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_27, x_28, x_31, x_1, x_33);
x_35 = lean_st_ref_set(x_22, x_34, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_41 = lean_mk_string_unchecked(": already registered", 20, 20);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_43);
return x_23;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_46 = l_Lean_Name_instBEq;
x_47 = l_Lean_instHashableName;
lean_inc(x_1);
x_48 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_46, x_47, x_44, x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_16);
lean_dec(x_15);
x_49 = lean_st_ref_take(x_22, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_Server_wrapRpcProcedure___redArg(x_1, x_2, x_3, x_4);
x_53 = l_Lean_PersistentHashMap_insert___redArg(x_46, x_47, x_50, x_1, x_52);
x_54 = lean_st_ref_set(x_22, x_53, x_51);
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
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_60 = lean_mk_string_unchecked(": already registered", 20, 20);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_45);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_6, 0);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_6);
x_66 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lam__0___boxed), 1, 0);
x_67 = lean_box(1);
x_68 = lean_mk_string_unchecked("Failed to register builtin RPC call handler for '", 49, 49);
x_69 = lean_unbox(x_67);
lean_inc(x_1);
x_70 = l_Lean_Name_toString(x_1, x_69, x_66);
x_71 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_72 = lean_mk_string_unchecked("'", 1, 1);
x_73 = lean_unbox(x_64);
lean_dec(x_64);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_75 = lean_mk_string_unchecked(": only possible during initialization", 37, 37);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = l_Lean_Server_builtinRpcProcedures;
x_80 = lean_st_ref_get(x_79, x_65);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Name_instBEq;
x_85 = l_Lean_instHashableName;
lean_inc(x_1);
x_86 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_84, x_85, x_81, x_1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_83);
lean_dec(x_72);
lean_dec(x_71);
x_87 = lean_st_ref_take(x_79, x_82);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_1);
x_90 = l_Lean_Server_wrapRpcProcedure___redArg(x_1, x_2, x_3, x_4);
x_91 = l_Lean_PersistentHashMap_insert___redArg(x_84, x_85, x_88, x_1, x_90);
x_92 = lean_st_ref_set(x_79, x_91, x_89);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_98 = lean_mk_string_unchecked(": already registered", 20, 20);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_100, 0, x_99);
if (lean_is_scalar(x_83)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_83;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_82);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_registerBuiltinRpcProcedure___redArg(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_58; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_9, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_9, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Environment_mainModule(x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_1);
x_26 = l_Lean_Name_mkStr4(x_1, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("wrapRpcProcedure", 16, 16);
lean_inc(x_27);
x_28 = l_String_toSubstring_x27(x_27);
lean_inc(x_27);
x_29 = l_Lean_Name_mkStr1(x_27);
x_30 = l_Lean_addMacroScope(x_22, x_29, x_20);
lean_inc(x_1);
x_31 = l_Lean_Name_mkStr3(x_1, x_2, x_27);
x_32 = lean_box(0);
lean_inc(x_31);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_19);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
lean_inc(x_3);
x_58 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_32, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_inc(x_3);
x_59 = l_Lean_quoteNameMk(x_3);
x_40 = x_59;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_1);
x_62 = l_Lean_Name_mkStr4(x_1, x_23, x_24, x_61);
x_63 = lean_mk_string_unchecked("`", 1, 1);
x_64 = lean_mk_string_unchecked(".", 1, 1);
x_65 = l_String_intercalate(x_64, x_60);
lean_dec(x_64);
x_66 = lean_string_append(x_63, x_65);
lean_dec(x_65);
x_67 = lean_box(2);
x_68 = l_Lean_Syntax_mkNameLit(x_66, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_mk_empty_array_with_capacity(x_69);
x_71 = lean_array_push(x_70, x_68);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_72, 2, x_71);
x_40 = x_72;
goto block_57;
}
block_57:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_41 = lean_mk_string_unchecked("hole", 4, 4);
x_42 = l_Lean_Name_mkStr4(x_1, x_23, x_24, x_41);
x_43 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node1(x_19, x_42, x_44);
x_46 = lean_mk_syntax_ident(x_3);
lean_inc(x_45);
lean_inc(x_19);
x_47 = l_Lean_Syntax_node4(x_19, x_39, x_40, x_45, x_45, x_46);
x_48 = l_Lean_Syntax_node2(x_19, x_26, x_37, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_4);
x_50 = lean_box(1);
x_51 = lean_unbox(x_50);
x_52 = lean_unbox(x_50);
lean_inc(x_8);
x_53 = l_Lean_Elab_Term_elabTerm(x_48, x_49, x_51, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_9);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_54, x_8, x_55);
lean_dec(x_8);
return x_56;
}
else
{
lean_dec(x_8);
return x_53;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_118; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_12);
x_75 = lean_ctor_get(x_9, 5);
lean_inc(x_75);
x_76 = lean_box(0);
x_77 = lean_unbox(x_76);
x_78 = l_Lean_SourceInfo_fromRef(x_75, x_77);
lean_dec(x_75);
x_79 = lean_ctor_get(x_9, 10);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = l_Lean_Environment_mainModule(x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked("Parser", 6, 6);
x_83 = lean_mk_string_unchecked("Term", 4, 4);
x_84 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_1);
x_85 = l_Lean_Name_mkStr4(x_1, x_82, x_83, x_84);
x_86 = lean_mk_string_unchecked("wrapRpcProcedure", 16, 16);
lean_inc(x_86);
x_87 = l_String_toSubstring_x27(x_86);
lean_inc(x_86);
x_88 = l_Lean_Name_mkStr1(x_86);
x_89 = l_Lean_addMacroScope(x_81, x_88, x_79);
lean_inc(x_1);
x_90 = l_Lean_Name_mkStr3(x_1, x_2, x_86);
x_91 = lean_box(0);
lean_inc(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_78);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_78);
lean_ctor_set(x_97, 1, x_87);
lean_ctor_set(x_97, 2, x_89);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
lean_inc(x_3);
x_118 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_91, x_3);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_inc(x_3);
x_119 = l_Lean_quoteNameMk(x_3);
x_100 = x_119;
goto block_117;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_1);
x_122 = l_Lean_Name_mkStr4(x_1, x_82, x_83, x_121);
x_123 = lean_mk_string_unchecked("`", 1, 1);
x_124 = lean_mk_string_unchecked(".", 1, 1);
x_125 = l_String_intercalate(x_124, x_120);
lean_dec(x_124);
x_126 = lean_string_append(x_123, x_125);
lean_dec(x_125);
x_127 = lean_box(2);
x_128 = l_Lean_Syntax_mkNameLit(x_126, x_127);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_mk_empty_array_with_capacity(x_129);
x_131 = lean_array_push(x_130, x_128);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_122);
lean_ctor_set(x_132, 2, x_131);
x_100 = x_132;
goto block_117;
}
block_117:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; 
x_101 = lean_mk_string_unchecked("hole", 4, 4);
x_102 = l_Lean_Name_mkStr4(x_1, x_82, x_83, x_101);
x_103 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_78);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_78);
x_105 = l_Lean_Syntax_node1(x_78, x_102, x_104);
x_106 = lean_mk_syntax_ident(x_3);
lean_inc(x_105);
lean_inc(x_78);
x_107 = l_Lean_Syntax_node4(x_78, x_99, x_100, x_105, x_105, x_106);
x_108 = l_Lean_Syntax_node2(x_78, x_85, x_97, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_4);
x_110 = lean_box(1);
x_111 = lean_unbox(x_110);
x_112 = lean_unbox(x_110);
lean_inc(x_8);
x_113 = l_Lean_Elab_Term_elabTerm(x_108, x_109, x_111, x_112, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_114, x_8, x_115);
lean_dec(x_8);
return x_116;
}
else
{
lean_dec(x_8);
return x_113;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lam__2(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Server_registerRpcProcedure___lam__0(x_7, x_2, x_3, x_8);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_mk_string_unchecked("Failed to register RPC call handler for '", 41, 41);
x_14 = l_Lean_Server_builtinRpcProcedures;
x_15 = lean_st_ref_get(x_14, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
lean_inc(x_1);
x_20 = l_Lean_MessageData_ofName(x_1);
x_21 = lean_mk_string_unchecked("'", 1, 1);
x_22 = lean_box(0);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_19);
x_23 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_15);
x_24 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_17, x_1);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Server_userRpcProcedures;
lean_inc(x_1);
x_26 = l_Lean_MapDeclarationExtension_contains___redArg(x_22, x_25, x_11, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_9);
lean_free_object(x_5);
x_27 = lean_mk_string_unchecked("_private", 8, 8);
x_28 = l_Lean_Name_str___override(x_22, x_27);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_29);
x_30 = l_Lean_Name_str___override(x_28, x_29);
x_31 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_31);
x_32 = l_Lean_Name_str___override(x_30, x_31);
x_33 = lean_mk_string_unchecked("Rpc", 3, 3);
x_34 = l_Lean_Name_str___override(x_32, x_33);
x_35 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_36 = l_Lean_Name_str___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_unsigned_to_nat(5u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_to_nat(x_40);
x_42 = lean_nat_pow(x_38, x_41);
lean_dec(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_usize_to_nat(x_43);
x_45 = lean_box(0);
x_46 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_46);
lean_inc(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
lean_inc(x_46);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_46);
lean_inc(x_46);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_46);
lean_inc(x_46);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_46);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_37);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_48);
lean_ctor_set(x_53, 5, x_49);
lean_ctor_set(x_53, 6, x_50);
lean_ctor_set(x_53, 7, x_51);
lean_ctor_set(x_53, 8, x_52);
lean_inc(x_46);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_46);
lean_inc(x_46);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_46);
lean_inc(x_46);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_46);
lean_inc(x_46);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_46);
lean_inc(x_57);
lean_inc(x_54);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_57);
x_59 = lean_mk_empty_array_with_capacity(x_44);
lean_dec(x_44);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_59);
x_61 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_37);
lean_ctor_set(x_61, 3, x_37);
lean_ctor_set_usize(x_61, 4, x_40);
lean_inc(x_46);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_46);
lean_inc_n(x_47, 2);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_47);
lean_ctor_set(x_63, 1, x_47);
lean_ctor_set(x_63, 2, x_47);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set(x_64, 2, x_45);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_63);
x_65 = lean_st_mk_ref(x_64, x_18);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Name_num___override(x_36, x_37);
lean_inc(x_29);
x_69 = l_Lean_Name_str___override(x_68, x_29);
lean_inc(x_31);
x_70 = l_Lean_Name_str___override(x_69, x_31);
x_71 = lean_mk_string_unchecked("RpcProcedure", 12, 12);
lean_inc(x_59);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_59);
x_73 = l_Lean_Name_str___override(x_70, x_71);
x_74 = lean_box(0);
lean_inc(x_59);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_59);
x_76 = lean_box(1);
x_77 = lean_box(0);
x_78 = lean_box(2);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_46);
lean_inc(x_59);
x_80 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_59);
lean_ctor_set(x_80, 2, x_37);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set_usize(x_80, 4, x_40);
x_81 = l_Lean_Expr_const___override(x_73, x_74);
lean_inc(x_81);
lean_inc(x_1);
x_82 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1), 11, 4);
lean_closure_set(x_82, 0, x_29);
lean_closure_set(x_82, 1, x_31);
lean_closure_set(x_82, 2, x_1);
lean_closure_set(x_82, 3, x_81);
x_83 = lean_box(0);
x_84 = lean_box(0);
x_85 = lean_box(1);
x_86 = lean_box(x_26);
x_87 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__2___boxed), 2, 1);
lean_closure_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_59);
lean_ctor_set(x_88, 2, x_37);
lean_ctor_set(x_88, 3, x_37);
lean_ctor_set_usize(x_88, 4, x_40);
x_89 = lean_box(0);
x_90 = lean_box(0);
x_91 = lean_box(0);
x_92 = lean_box(0);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_94, 0, x_26);
lean_ctor_set_uint8(x_94, 1, x_26);
lean_ctor_set_uint8(x_94, 2, x_26);
lean_ctor_set_uint8(x_94, 3, x_26);
lean_ctor_set_uint8(x_94, 4, x_26);
x_95 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 5, x_95);
x_96 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 6, x_96);
lean_ctor_set_uint8(x_94, 7, x_26);
x_97 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 8, x_97);
x_98 = lean_unbox(x_76);
lean_ctor_set_uint8(x_94, 9, x_98);
x_99 = lean_unbox(x_77);
lean_ctor_set_uint8(x_94, 10, x_99);
x_100 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 11, x_100);
x_101 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 12, x_101);
x_102 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 13, x_102);
x_103 = lean_unbox(x_78);
lean_ctor_set_uint8(x_94, 14, x_103);
x_104 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 15, x_104);
x_105 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 16, x_105);
x_106 = lean_unbox(x_85);
lean_ctor_set_uint8(x_94, 17, x_106);
x_107 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_94);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_79);
lean_ctor_set(x_108, 1, x_80);
lean_ctor_set(x_108, 2, x_45);
x_109 = lean_mk_empty_array_with_capacity(x_37);
x_110 = lean_box(0);
x_111 = lean_box(0);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed), 9, 2);
lean_closure_set(x_112, 0, lean_box(0));
lean_closure_set(x_112, 1, x_82);
x_113 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_113, 0, x_83);
lean_ctor_set(x_113, 1, x_84);
lean_ctor_set(x_113, 2, x_88);
lean_ctor_set(x_113, 3, x_87);
lean_ctor_set(x_113, 4, x_45);
lean_ctor_set(x_113, 5, x_45);
lean_ctor_set(x_113, 6, x_89);
x_114 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7, x_114);
x_115 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 1, x_115);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 2, x_26);
x_116 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 3, x_116);
x_117 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 4, x_117);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 6, x_26);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 7, x_26);
x_118 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 8, x_118);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 9, x_26);
x_119 = lean_unbox(x_85);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 10, x_119);
x_120 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_120, 0, x_90);
lean_ctor_set(x_120, 1, x_45);
lean_ctor_set(x_120, 2, x_90);
lean_ctor_set(x_120, 3, x_91);
lean_ctor_set(x_120, 4, x_92);
lean_ctor_set(x_120, 5, x_45);
lean_ctor_set(x_120, 6, x_93);
x_121 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_121, 0, x_94);
lean_ctor_set(x_121, 1, x_45);
lean_ctor_set(x_121, 2, x_108);
lean_ctor_set(x_121, 3, x_109);
lean_ctor_set(x_121, 4, x_110);
lean_ctor_set(x_121, 5, x_37);
lean_ctor_set(x_121, 6, x_111);
lean_ctor_set_uint64(x_121, sizeof(void*)*7, x_107);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 8, x_26);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 9, x_26);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 10, x_26);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_66);
x_122 = l_Lean_Elab_Term_TermElabM_run___redArg(x_112, x_113, x_120, x_121, x_66, x_2, x_3, x_67);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_66, x_124);
lean_dec(x_66);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
x_127 = lean_ctor_get(x_125, 1);
x_128 = lean_ctor_get(x_125, 0);
lean_dec(x_128);
x_129 = lean_mk_string_unchecked("_rpc_wrapped", 12, 12);
x_130 = l_Lean_Name_mkStr1(x_129);
lean_inc(x_1);
x_131 = l_Lean_Name_append(x_1, x_130);
x_132 = lean_ctor_get(x_123, 0);
lean_inc(x_132);
lean_dec(x_123);
lean_inc(x_131);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_90);
lean_ctor_set(x_133, 2, x_81);
x_134 = lean_box(0);
x_135 = lean_box(1);
lean_inc(x_131);
lean_ctor_set_tag(x_125, 1);
lean_ctor_set(x_125, 1, x_90);
lean_ctor_set(x_125, 0, x_131);
x_136 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_125);
x_137 = lean_unbox(x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_137);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_136);
lean_inc(x_3);
lean_inc(x_2);
x_139 = l_Lean_addAndCompile(x_138, x_2, x_3, x_127);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_st_ref_get(x_3, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Server_registerRpcProcedure___lam__0(x_142, x_2, x_3, x_143);
lean_dec(x_2);
lean_dec(x_142);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_25, x_145, x_1, x_131);
x_148 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_147, x_3, x_146);
lean_dec(x_3);
return x_148;
}
else
{
lean_dec(x_131);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_139;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
x_149 = lean_ctor_get(x_125, 1);
lean_inc(x_149);
lean_dec(x_125);
x_150 = lean_mk_string_unchecked("_rpc_wrapped", 12, 12);
x_151 = l_Lean_Name_mkStr1(x_150);
lean_inc(x_1);
x_152 = l_Lean_Name_append(x_1, x_151);
x_153 = lean_ctor_get(x_123, 0);
lean_inc(x_153);
lean_dec(x_123);
lean_inc(x_152);
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_90);
lean_ctor_set(x_154, 2, x_81);
x_155 = lean_box(0);
x_156 = lean_box(1);
lean_inc(x_152);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_90);
x_158 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_155);
lean_ctor_set(x_158, 3, x_157);
x_159 = lean_unbox(x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_159);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_158);
lean_inc(x_3);
lean_inc(x_2);
x_161 = l_Lean_addAndCompile(x_160, x_2, x_3, x_149);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_st_ref_get(x_3, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Server_registerRpcProcedure___lam__0(x_164, x_2, x_3, x_165);
lean_dec(x_2);
lean_dec(x_164);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_25, x_167, x_1, x_152);
x_170 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_169, x_3, x_168);
lean_dec(x_3);
return x_170;
}
else
{
lean_dec(x_152);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_161;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_81);
lean_dec(x_66);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_122);
if (x_171 == 0)
{
return x_122;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_122, 0);
x_173 = lean_ctor_get(x_122, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_122);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_1);
x_175 = lean_mk_string_unchecked("", 0, 0);
x_176 = l_Lean_stringToMessageData(x_175);
lean_dec(x_175);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_176);
x_177 = lean_mk_string_unchecked(": already registered", 20, 20);
x_178 = l_Lean_stringToMessageData(x_177);
lean_dec(x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_5);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_179, x_2, x_3, x_18);
lean_dec(x_3);
lean_dec(x_2);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_11);
lean_dec(x_1);
x_181 = lean_mk_string_unchecked("", 0, 0);
x_182 = l_Lean_stringToMessageData(x_181);
lean_dec(x_181);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_182);
x_183 = lean_mk_string_unchecked(": already registered (builtin)", 30, 30);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_5);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_185, x_2, x_3, x_18);
lean_dec(x_3);
lean_dec(x_2);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_187 = lean_ctor_get(x_15, 0);
x_188 = lean_ctor_get(x_15, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_15);
x_189 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
lean_inc(x_1);
x_190 = l_Lean_MessageData_ofName(x_1);
x_191 = lean_mk_string_unchecked("'", 1, 1);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_189);
lean_ctor_set(x_193, 1, x_190);
x_194 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_194);
lean_ctor_set(x_9, 0, x_193);
x_195 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_187, x_1);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = l_Lean_Server_userRpcProcedures;
lean_inc(x_1);
x_197 = l_Lean_MapDeclarationExtension_contains___redArg(x_192, x_196, x_11, x_1);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; size_t x_211; lean_object* x_212; lean_object* x_213; size_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint64_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_9);
lean_free_object(x_5);
x_198 = lean_mk_string_unchecked("_private", 8, 8);
x_199 = l_Lean_Name_str___override(x_192, x_198);
x_200 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_200);
x_201 = l_Lean_Name_str___override(x_199, x_200);
x_202 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_202);
x_203 = l_Lean_Name_str___override(x_201, x_202);
x_204 = lean_mk_string_unchecked("Rpc", 3, 3);
x_205 = l_Lean_Name_str___override(x_203, x_204);
x_206 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_207 = l_Lean_Name_str___override(x_205, x_206);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_unsigned_to_nat(2u);
x_210 = lean_unsigned_to_nat(5u);
x_211 = lean_usize_of_nat(x_210);
x_212 = lean_usize_to_nat(x_211);
x_213 = lean_nat_pow(x_209, x_212);
lean_dec(x_212);
x_214 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_215 = lean_usize_to_nat(x_214);
x_216 = lean_box(0);
x_217 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_217);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
lean_inc(x_217);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_217);
lean_inc(x_217);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_217);
lean_inc(x_217);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_217);
lean_inc(x_217);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_217);
lean_inc(x_217);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_217);
lean_inc(x_218);
x_224 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_224, 0, x_208);
lean_ctor_set(x_224, 1, x_208);
lean_ctor_set(x_224, 2, x_208);
lean_ctor_set(x_224, 3, x_218);
lean_ctor_set(x_224, 4, x_219);
lean_ctor_set(x_224, 5, x_220);
lean_ctor_set(x_224, 6, x_221);
lean_ctor_set(x_224, 7, x_222);
lean_ctor_set(x_224, 8, x_223);
lean_inc(x_217);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_217);
lean_inc(x_217);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_217);
lean_inc(x_217);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_217);
lean_inc(x_217);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_217);
lean_inc(x_228);
lean_inc(x_225);
x_229 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_226);
lean_ctor_set(x_229, 2, x_227);
lean_ctor_set(x_229, 3, x_225);
lean_ctor_set(x_229, 4, x_228);
lean_ctor_set(x_229, 5, x_228);
x_230 = lean_mk_empty_array_with_capacity(x_215);
lean_dec(x_215);
lean_inc(x_230);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_230);
lean_inc(x_230);
x_232 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
lean_ctor_set(x_232, 2, x_208);
lean_ctor_set(x_232, 3, x_208);
lean_ctor_set_usize(x_232, 4, x_211);
lean_inc(x_217);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_217);
lean_inc_n(x_218, 2);
x_234 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_234, 0, x_218);
lean_ctor_set(x_234, 1, x_218);
lean_ctor_set(x_234, 2, x_218);
lean_ctor_set(x_234, 3, x_233);
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_224);
lean_ctor_set(x_235, 1, x_229);
lean_ctor_set(x_235, 2, x_216);
lean_ctor_set(x_235, 3, x_232);
lean_ctor_set(x_235, 4, x_234);
x_236 = lean_st_mk_ref(x_235, x_188);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Name_num___override(x_207, x_208);
lean_inc(x_200);
x_240 = l_Lean_Name_str___override(x_239, x_200);
lean_inc(x_202);
x_241 = l_Lean_Name_str___override(x_240, x_202);
x_242 = lean_mk_string_unchecked("RpcProcedure", 12, 12);
lean_inc(x_230);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_230);
x_244 = l_Lean_Name_str___override(x_241, x_242);
x_245 = lean_box(0);
lean_inc(x_230);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_230);
x_247 = lean_box(1);
x_248 = lean_box(0);
x_249 = lean_box(2);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_217);
lean_inc(x_230);
x_251 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_230);
lean_ctor_set(x_251, 2, x_208);
lean_ctor_set(x_251, 3, x_208);
lean_ctor_set_usize(x_251, 4, x_211);
x_252 = l_Lean_Expr_const___override(x_244, x_245);
lean_inc(x_252);
lean_inc(x_1);
x_253 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1), 11, 4);
lean_closure_set(x_253, 0, x_200);
lean_closure_set(x_253, 1, x_202);
lean_closure_set(x_253, 2, x_1);
lean_closure_set(x_253, 3, x_252);
x_254 = lean_box(0);
x_255 = lean_box(0);
x_256 = lean_box(1);
x_257 = lean_box(x_197);
x_258 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__2___boxed), 2, 1);
lean_closure_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_259, 0, x_246);
lean_ctor_set(x_259, 1, x_230);
lean_ctor_set(x_259, 2, x_208);
lean_ctor_set(x_259, 3, x_208);
lean_ctor_set_usize(x_259, 4, x_211);
x_260 = lean_box(0);
x_261 = lean_box(0);
x_262 = lean_box(0);
x_263 = lean_box(0);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_265, 0, x_197);
lean_ctor_set_uint8(x_265, 1, x_197);
lean_ctor_set_uint8(x_265, 2, x_197);
lean_ctor_set_uint8(x_265, 3, x_197);
lean_ctor_set_uint8(x_265, 4, x_197);
x_266 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 5, x_266);
x_267 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 6, x_267);
lean_ctor_set_uint8(x_265, 7, x_197);
x_268 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 8, x_268);
x_269 = lean_unbox(x_247);
lean_ctor_set_uint8(x_265, 9, x_269);
x_270 = lean_unbox(x_248);
lean_ctor_set_uint8(x_265, 10, x_270);
x_271 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 11, x_271);
x_272 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 12, x_272);
x_273 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 13, x_273);
x_274 = lean_unbox(x_249);
lean_ctor_set_uint8(x_265, 14, x_274);
x_275 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 15, x_275);
x_276 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 16, x_276);
x_277 = lean_unbox(x_256);
lean_ctor_set_uint8(x_265, 17, x_277);
x_278 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_265);
x_279 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_279, 0, x_250);
lean_ctor_set(x_279, 1, x_251);
lean_ctor_set(x_279, 2, x_216);
x_280 = lean_mk_empty_array_with_capacity(x_208);
x_281 = lean_box(0);
x_282 = lean_box(0);
x_283 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed), 9, 2);
lean_closure_set(x_283, 0, lean_box(0));
lean_closure_set(x_283, 1, x_253);
x_284 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_284, 0, x_254);
lean_ctor_set(x_284, 1, x_255);
lean_ctor_set(x_284, 2, x_259);
lean_ctor_set(x_284, 3, x_258);
lean_ctor_set(x_284, 4, x_216);
lean_ctor_set(x_284, 5, x_216);
lean_ctor_set(x_284, 6, x_260);
x_285 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7, x_285);
x_286 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 1, x_286);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 2, x_197);
x_287 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 3, x_287);
x_288 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 4, x_288);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 5, x_197);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 6, x_197);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 7, x_197);
x_289 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 8, x_289);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 9, x_197);
x_290 = lean_unbox(x_256);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 10, x_290);
x_291 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_291, 0, x_261);
lean_ctor_set(x_291, 1, x_216);
lean_ctor_set(x_291, 2, x_261);
lean_ctor_set(x_291, 3, x_262);
lean_ctor_set(x_291, 4, x_263);
lean_ctor_set(x_291, 5, x_216);
lean_ctor_set(x_291, 6, x_264);
x_292 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_292, 0, x_265);
lean_ctor_set(x_292, 1, x_216);
lean_ctor_set(x_292, 2, x_279);
lean_ctor_set(x_292, 3, x_280);
lean_ctor_set(x_292, 4, x_281);
lean_ctor_set(x_292, 5, x_208);
lean_ctor_set(x_292, 6, x_282);
lean_ctor_set_uint64(x_292, sizeof(void*)*7, x_278);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 8, x_197);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 9, x_197);
lean_ctor_set_uint8(x_292, sizeof(void*)*7 + 10, x_197);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_237);
x_293 = l_Lean_Elab_Term_TermElabM_run___redArg(x_283, x_284, x_291, x_292, x_237, x_2, x_3, x_238);
lean_dec(x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_st_ref_get(x_237, x_295);
lean_dec(x_237);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
x_299 = lean_mk_string_unchecked("_rpc_wrapped", 12, 12);
x_300 = l_Lean_Name_mkStr1(x_299);
lean_inc(x_1);
x_301 = l_Lean_Name_append(x_1, x_300);
x_302 = lean_ctor_get(x_294, 0);
lean_inc(x_302);
lean_dec(x_294);
lean_inc(x_301);
x_303 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_261);
lean_ctor_set(x_303, 2, x_252);
x_304 = lean_box(0);
x_305 = lean_box(1);
lean_inc(x_301);
if (lean_is_scalar(x_298)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_298;
 lean_ctor_set_tag(x_306, 1);
}
lean_ctor_set(x_306, 0, x_301);
lean_ctor_set(x_306, 1, x_261);
x_307 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_302);
lean_ctor_set(x_307, 2, x_304);
lean_ctor_set(x_307, 3, x_306);
x_308 = lean_unbox(x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*4, x_308);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_307);
lean_inc(x_3);
lean_inc(x_2);
x_310 = l_Lean_addAndCompile(x_309, x_2, x_3, x_297);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_st_ref_get(x_3, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l_Lean_Server_registerRpcProcedure___lam__0(x_313, x_2, x_3, x_314);
lean_dec(x_2);
lean_dec(x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_196, x_316, x_1, x_301);
x_319 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_318, x_3, x_317);
lean_dec(x_3);
return x_319;
}
else
{
lean_dec(x_301);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_310;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_252);
lean_dec(x_237);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_293, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_293, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_322 = x_293;
} else {
 lean_dec_ref(x_293);
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
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_1);
x_324 = lean_mk_string_unchecked("", 0, 0);
x_325 = l_Lean_stringToMessageData(x_324);
lean_dec(x_324);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_325);
x_326 = lean_mk_string_unchecked(": already registered", 20, 20);
x_327 = l_Lean_stringToMessageData(x_326);
lean_dec(x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_5);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_328, x_2, x_3, x_188);
lean_dec(x_3);
lean_dec(x_2);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_11);
lean_dec(x_1);
x_330 = lean_mk_string_unchecked("", 0, 0);
x_331 = l_Lean_stringToMessageData(x_330);
lean_dec(x_330);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_331);
x_332 = lean_mk_string_unchecked(": already registered (builtin)", 30, 30);
x_333 = l_Lean_stringToMessageData(x_332);
lean_dec(x_332);
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_5);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_334, x_2, x_3, x_188);
lean_dec(x_3);
lean_dec(x_2);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_336 = lean_ctor_get(x_9, 0);
x_337 = lean_ctor_get(x_9, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_9);
x_338 = lean_mk_string_unchecked("Failed to register RPC call handler for '", 41, 41);
x_339 = l_Lean_Server_builtinRpcProcedures;
x_340 = lean_st_ref_get(x_339, x_337);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
x_344 = l_Lean_stringToMessageData(x_338);
lean_dec(x_338);
lean_inc(x_1);
x_345 = l_Lean_MessageData_ofName(x_1);
x_346 = lean_mk_string_unchecked("'", 1, 1);
x_347 = lean_box(0);
if (lean_is_scalar(x_343)) {
 x_348 = lean_alloc_ctor(7, 2, 0);
} else {
 x_348 = x_343;
 lean_ctor_set_tag(x_348, 7);
}
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
x_349 = l_Lean_stringToMessageData(x_346);
lean_dec(x_346);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_341, x_1);
if (x_351 == 0)
{
lean_object* x_352; uint8_t x_353; 
x_352 = l_Lean_Server_userRpcProcedures;
lean_inc(x_1);
x_353 = l_Lean_MapDeclarationExtension_contains___redArg(x_347, x_352, x_336, x_1);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; size_t x_367; lean_object* x_368; lean_object* x_369; size_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; uint8_t x_426; uint8_t x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint64_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; uint8_t x_442; uint8_t x_443; uint8_t x_444; uint8_t x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_350);
lean_free_object(x_5);
x_354 = lean_mk_string_unchecked("_private", 8, 8);
x_355 = l_Lean_Name_str___override(x_347, x_354);
x_356 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_356);
x_357 = l_Lean_Name_str___override(x_355, x_356);
x_358 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_358);
x_359 = l_Lean_Name_str___override(x_357, x_358);
x_360 = lean_mk_string_unchecked("Rpc", 3, 3);
x_361 = l_Lean_Name_str___override(x_359, x_360);
x_362 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_363 = l_Lean_Name_str___override(x_361, x_362);
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_unsigned_to_nat(2u);
x_366 = lean_unsigned_to_nat(5u);
x_367 = lean_usize_of_nat(x_366);
x_368 = lean_usize_to_nat(x_367);
x_369 = lean_nat_pow(x_365, x_368);
lean_dec(x_368);
x_370 = lean_usize_of_nat(x_369);
lean_dec(x_369);
x_371 = lean_usize_to_nat(x_370);
x_372 = lean_box(0);
x_373 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_373);
x_374 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_374, 0, x_373);
lean_inc(x_373);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_373);
lean_inc(x_373);
x_376 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_376, 0, x_373);
lean_inc(x_373);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_373);
lean_inc(x_373);
x_378 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_378, 0, x_373);
lean_inc(x_373);
x_379 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_379, 0, x_373);
lean_inc(x_374);
x_380 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_380, 0, x_364);
lean_ctor_set(x_380, 1, x_364);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_374);
lean_ctor_set(x_380, 4, x_375);
lean_ctor_set(x_380, 5, x_376);
lean_ctor_set(x_380, 6, x_377);
lean_ctor_set(x_380, 7, x_378);
lean_ctor_set(x_380, 8, x_379);
lean_inc(x_373);
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_373);
lean_inc(x_373);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_373);
lean_inc(x_373);
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_373);
lean_inc(x_373);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_373);
lean_inc(x_384);
lean_inc(x_381);
x_385 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_385, 0, x_381);
lean_ctor_set(x_385, 1, x_382);
lean_ctor_set(x_385, 2, x_383);
lean_ctor_set(x_385, 3, x_381);
lean_ctor_set(x_385, 4, x_384);
lean_ctor_set(x_385, 5, x_384);
x_386 = lean_mk_empty_array_with_capacity(x_371);
lean_dec(x_371);
lean_inc(x_386);
x_387 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_387, 0, x_386);
lean_inc(x_386);
x_388 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
lean_ctor_set(x_388, 2, x_364);
lean_ctor_set(x_388, 3, x_364);
lean_ctor_set_usize(x_388, 4, x_367);
lean_inc(x_373);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_373);
lean_inc_n(x_374, 2);
x_390 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_390, 0, x_374);
lean_ctor_set(x_390, 1, x_374);
lean_ctor_set(x_390, 2, x_374);
lean_ctor_set(x_390, 3, x_389);
x_391 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_391, 0, x_380);
lean_ctor_set(x_391, 1, x_385);
lean_ctor_set(x_391, 2, x_372);
lean_ctor_set(x_391, 3, x_388);
lean_ctor_set(x_391, 4, x_390);
x_392 = lean_st_mk_ref(x_391, x_342);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = l_Lean_Name_num___override(x_363, x_364);
lean_inc(x_356);
x_396 = l_Lean_Name_str___override(x_395, x_356);
lean_inc(x_358);
x_397 = l_Lean_Name_str___override(x_396, x_358);
x_398 = lean_mk_string_unchecked("RpcProcedure", 12, 12);
lean_inc(x_386);
x_399 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_399, 0, x_386);
x_400 = l_Lean_Name_str___override(x_397, x_398);
x_401 = lean_box(0);
lean_inc(x_386);
x_402 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_402, 0, x_386);
x_403 = lean_box(1);
x_404 = lean_box(0);
x_405 = lean_box(2);
x_406 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_406, 0, x_373);
lean_inc(x_386);
x_407 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_407, 0, x_399);
lean_ctor_set(x_407, 1, x_386);
lean_ctor_set(x_407, 2, x_364);
lean_ctor_set(x_407, 3, x_364);
lean_ctor_set_usize(x_407, 4, x_367);
x_408 = l_Lean_Expr_const___override(x_400, x_401);
lean_inc(x_408);
lean_inc(x_1);
x_409 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1), 11, 4);
lean_closure_set(x_409, 0, x_356);
lean_closure_set(x_409, 1, x_358);
lean_closure_set(x_409, 2, x_1);
lean_closure_set(x_409, 3, x_408);
x_410 = lean_box(0);
x_411 = lean_box(0);
x_412 = lean_box(1);
x_413 = lean_box(x_353);
x_414 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__2___boxed), 2, 1);
lean_closure_set(x_414, 0, x_413);
x_415 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_415, 0, x_402);
lean_ctor_set(x_415, 1, x_386);
lean_ctor_set(x_415, 2, x_364);
lean_ctor_set(x_415, 3, x_364);
lean_ctor_set_usize(x_415, 4, x_367);
x_416 = lean_box(0);
x_417 = lean_box(0);
x_418 = lean_box(0);
x_419 = lean_box(0);
x_420 = lean_box(0);
x_421 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_421, 0, x_353);
lean_ctor_set_uint8(x_421, 1, x_353);
lean_ctor_set_uint8(x_421, 2, x_353);
lean_ctor_set_uint8(x_421, 3, x_353);
lean_ctor_set_uint8(x_421, 4, x_353);
x_422 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 5, x_422);
x_423 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 6, x_423);
lean_ctor_set_uint8(x_421, 7, x_353);
x_424 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 8, x_424);
x_425 = lean_unbox(x_403);
lean_ctor_set_uint8(x_421, 9, x_425);
x_426 = lean_unbox(x_404);
lean_ctor_set_uint8(x_421, 10, x_426);
x_427 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 11, x_427);
x_428 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 12, x_428);
x_429 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 13, x_429);
x_430 = lean_unbox(x_405);
lean_ctor_set_uint8(x_421, 14, x_430);
x_431 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 15, x_431);
x_432 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 16, x_432);
x_433 = lean_unbox(x_412);
lean_ctor_set_uint8(x_421, 17, x_433);
x_434 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_421);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_406);
lean_ctor_set(x_435, 1, x_407);
lean_ctor_set(x_435, 2, x_372);
x_436 = lean_mk_empty_array_with_capacity(x_364);
x_437 = lean_box(0);
x_438 = lean_box(0);
x_439 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed), 9, 2);
lean_closure_set(x_439, 0, lean_box(0));
lean_closure_set(x_439, 1, x_409);
x_440 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_440, 0, x_410);
lean_ctor_set(x_440, 1, x_411);
lean_ctor_set(x_440, 2, x_415);
lean_ctor_set(x_440, 3, x_414);
lean_ctor_set(x_440, 4, x_372);
lean_ctor_set(x_440, 5, x_372);
lean_ctor_set(x_440, 6, x_416);
x_441 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7, x_441);
x_442 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 1, x_442);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 2, x_353);
x_443 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 3, x_443);
x_444 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 4, x_444);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 5, x_353);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 6, x_353);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 7, x_353);
x_445 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 8, x_445);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 9, x_353);
x_446 = lean_unbox(x_412);
lean_ctor_set_uint8(x_440, sizeof(void*)*7 + 10, x_446);
x_447 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_447, 0, x_417);
lean_ctor_set(x_447, 1, x_372);
lean_ctor_set(x_447, 2, x_417);
lean_ctor_set(x_447, 3, x_418);
lean_ctor_set(x_447, 4, x_419);
lean_ctor_set(x_447, 5, x_372);
lean_ctor_set(x_447, 6, x_420);
x_448 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_448, 0, x_421);
lean_ctor_set(x_448, 1, x_372);
lean_ctor_set(x_448, 2, x_435);
lean_ctor_set(x_448, 3, x_436);
lean_ctor_set(x_448, 4, x_437);
lean_ctor_set(x_448, 5, x_364);
lean_ctor_set(x_448, 6, x_438);
lean_ctor_set_uint64(x_448, sizeof(void*)*7, x_434);
lean_ctor_set_uint8(x_448, sizeof(void*)*7 + 8, x_353);
lean_ctor_set_uint8(x_448, sizeof(void*)*7 + 9, x_353);
lean_ctor_set_uint8(x_448, sizeof(void*)*7 + 10, x_353);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_393);
x_449 = l_Lean_Elab_Term_TermElabM_run___redArg(x_439, x_440, x_447, x_448, x_393, x_2, x_3, x_394);
lean_dec(x_448);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_st_ref_get(x_393, x_451);
lean_dec(x_393);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
x_455 = lean_mk_string_unchecked("_rpc_wrapped", 12, 12);
x_456 = l_Lean_Name_mkStr1(x_455);
lean_inc(x_1);
x_457 = l_Lean_Name_append(x_1, x_456);
x_458 = lean_ctor_get(x_450, 0);
lean_inc(x_458);
lean_dec(x_450);
lean_inc(x_457);
x_459 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_417);
lean_ctor_set(x_459, 2, x_408);
x_460 = lean_box(0);
x_461 = lean_box(1);
lean_inc(x_457);
if (lean_is_scalar(x_454)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_454;
 lean_ctor_set_tag(x_462, 1);
}
lean_ctor_set(x_462, 0, x_457);
lean_ctor_set(x_462, 1, x_417);
x_463 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_458);
lean_ctor_set(x_463, 2, x_460);
lean_ctor_set(x_463, 3, x_462);
x_464 = lean_unbox(x_461);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_464);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_463);
lean_inc(x_3);
lean_inc(x_2);
x_466 = l_Lean_addAndCompile(x_465, x_2, x_3, x_453);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = lean_st_ref_get(x_3, x_467);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = l_Lean_Server_registerRpcProcedure___lam__0(x_469, x_2, x_3, x_470);
lean_dec(x_2);
lean_dec(x_469);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_474 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_352, x_472, x_1, x_457);
x_475 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_474, x_3, x_473);
lean_dec(x_3);
return x_475;
}
else
{
lean_dec(x_457);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_466;
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_408);
lean_dec(x_393);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_476 = lean_ctor_get(x_449, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_449, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_478 = x_449;
} else {
 lean_dec_ref(x_449);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_1);
x_480 = lean_mk_string_unchecked("", 0, 0);
x_481 = l_Lean_stringToMessageData(x_480);
lean_dec(x_480);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_350);
lean_ctor_set(x_5, 0, x_481);
x_482 = lean_mk_string_unchecked(": already registered", 20, 20);
x_483 = l_Lean_stringToMessageData(x_482);
lean_dec(x_482);
x_484 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_484, 0, x_5);
lean_ctor_set(x_484, 1, x_483);
x_485 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_484, x_2, x_3, x_342);
lean_dec(x_3);
lean_dec(x_2);
return x_485;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_336);
lean_dec(x_1);
x_486 = lean_mk_string_unchecked("", 0, 0);
x_487 = l_Lean_stringToMessageData(x_486);
lean_dec(x_486);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_350);
lean_ctor_set(x_5, 0, x_487);
x_488 = lean_mk_string_unchecked(": already registered (builtin)", 30, 30);
x_489 = l_Lean_stringToMessageData(x_488);
lean_dec(x_488);
x_490 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_490, 0, x_5);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_490, x_2, x_3, x_342);
lean_dec(x_3);
lean_dec(x_2);
return x_491;
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_492 = lean_ctor_get(x_5, 0);
x_493 = lean_ctor_get(x_5, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_5);
x_494 = l_Lean_Server_registerRpcProcedure___lam__0(x_492, x_2, x_3, x_493);
lean_dec(x_492);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_497 = x_494;
} else {
 lean_dec_ref(x_494);
 x_497 = lean_box(0);
}
x_498 = lean_mk_string_unchecked("Failed to register RPC call handler for '", 41, 41);
x_499 = l_Lean_Server_builtinRpcProcedures;
x_500 = lean_st_ref_get(x_499, x_496);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = l_Lean_stringToMessageData(x_498);
lean_dec(x_498);
lean_inc(x_1);
x_505 = l_Lean_MessageData_ofName(x_1);
x_506 = lean_mk_string_unchecked("'", 1, 1);
x_507 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_508 = lean_alloc_ctor(7, 2, 0);
} else {
 x_508 = x_503;
 lean_ctor_set_tag(x_508, 7);
}
lean_ctor_set(x_508, 0, x_504);
lean_ctor_set(x_508, 1, x_505);
x_509 = l_Lean_stringToMessageData(x_506);
lean_dec(x_506);
if (lean_is_scalar(x_497)) {
 x_510 = lean_alloc_ctor(7, 2, 0);
} else {
 x_510 = x_497;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
x_511 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_501, x_1);
if (x_511 == 0)
{
lean_object* x_512; uint8_t x_513; 
x_512 = l_Lean_Server_userRpcProcedures;
lean_inc(x_1);
x_513 = l_Lean_MapDeclarationExtension_contains___redArg(x_507, x_512, x_495, x_1);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; size_t x_527; lean_object* x_528; lean_object* x_529; size_t x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; uint8_t x_583; uint8_t x_584; uint8_t x_585; uint8_t x_586; uint8_t x_587; uint8_t x_588; uint8_t x_589; uint8_t x_590; uint8_t x_591; uint8_t x_592; uint8_t x_593; uint64_t x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; uint8_t x_602; uint8_t x_603; uint8_t x_604; uint8_t x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_510);
x_514 = lean_mk_string_unchecked("_private", 8, 8);
x_515 = l_Lean_Name_str___override(x_507, x_514);
x_516 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_516);
x_517 = l_Lean_Name_str___override(x_515, x_516);
x_518 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_518);
x_519 = l_Lean_Name_str___override(x_517, x_518);
x_520 = lean_mk_string_unchecked("Rpc", 3, 3);
x_521 = l_Lean_Name_str___override(x_519, x_520);
x_522 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_523 = l_Lean_Name_str___override(x_521, x_522);
x_524 = lean_unsigned_to_nat(0u);
x_525 = lean_unsigned_to_nat(2u);
x_526 = lean_unsigned_to_nat(5u);
x_527 = lean_usize_of_nat(x_526);
x_528 = lean_usize_to_nat(x_527);
x_529 = lean_nat_pow(x_525, x_528);
lean_dec(x_528);
x_530 = lean_usize_of_nat(x_529);
lean_dec(x_529);
x_531 = lean_usize_to_nat(x_530);
x_532 = lean_box(0);
x_533 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_533);
x_534 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_534, 0, x_533);
lean_inc(x_533);
x_535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_535, 0, x_533);
lean_inc(x_533);
x_536 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_536, 0, x_533);
lean_inc(x_533);
x_537 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_537, 0, x_533);
lean_inc(x_533);
x_538 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_538, 0, x_533);
lean_inc(x_533);
x_539 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_539, 0, x_533);
lean_inc(x_534);
x_540 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_540, 0, x_524);
lean_ctor_set(x_540, 1, x_524);
lean_ctor_set(x_540, 2, x_524);
lean_ctor_set(x_540, 3, x_534);
lean_ctor_set(x_540, 4, x_535);
lean_ctor_set(x_540, 5, x_536);
lean_ctor_set(x_540, 6, x_537);
lean_ctor_set(x_540, 7, x_538);
lean_ctor_set(x_540, 8, x_539);
lean_inc(x_533);
x_541 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_541, 0, x_533);
lean_inc(x_533);
x_542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_542, 0, x_533);
lean_inc(x_533);
x_543 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_543, 0, x_533);
lean_inc(x_533);
x_544 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_544, 0, x_533);
lean_inc(x_544);
lean_inc(x_541);
x_545 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_545, 0, x_541);
lean_ctor_set(x_545, 1, x_542);
lean_ctor_set(x_545, 2, x_543);
lean_ctor_set(x_545, 3, x_541);
lean_ctor_set(x_545, 4, x_544);
lean_ctor_set(x_545, 5, x_544);
x_546 = lean_mk_empty_array_with_capacity(x_531);
lean_dec(x_531);
lean_inc(x_546);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_546);
lean_inc(x_546);
x_548 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_546);
lean_ctor_set(x_548, 2, x_524);
lean_ctor_set(x_548, 3, x_524);
lean_ctor_set_usize(x_548, 4, x_527);
lean_inc(x_533);
x_549 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_549, 0, x_533);
lean_inc_n(x_534, 2);
x_550 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_550, 0, x_534);
lean_ctor_set(x_550, 1, x_534);
lean_ctor_set(x_550, 2, x_534);
lean_ctor_set(x_550, 3, x_549);
x_551 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_551, 0, x_540);
lean_ctor_set(x_551, 1, x_545);
lean_ctor_set(x_551, 2, x_532);
lean_ctor_set(x_551, 3, x_548);
lean_ctor_set(x_551, 4, x_550);
x_552 = lean_st_mk_ref(x_551, x_502);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = l_Lean_Name_num___override(x_523, x_524);
lean_inc(x_516);
x_556 = l_Lean_Name_str___override(x_555, x_516);
lean_inc(x_518);
x_557 = l_Lean_Name_str___override(x_556, x_518);
x_558 = lean_mk_string_unchecked("RpcProcedure", 12, 12);
lean_inc(x_546);
x_559 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_559, 0, x_546);
x_560 = l_Lean_Name_str___override(x_557, x_558);
x_561 = lean_box(0);
lean_inc(x_546);
x_562 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_562, 0, x_546);
x_563 = lean_box(1);
x_564 = lean_box(0);
x_565 = lean_box(2);
x_566 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_566, 0, x_533);
lean_inc(x_546);
x_567 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_567, 0, x_559);
lean_ctor_set(x_567, 1, x_546);
lean_ctor_set(x_567, 2, x_524);
lean_ctor_set(x_567, 3, x_524);
lean_ctor_set_usize(x_567, 4, x_527);
x_568 = l_Lean_Expr_const___override(x_560, x_561);
lean_inc(x_568);
lean_inc(x_1);
x_569 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__1), 11, 4);
lean_closure_set(x_569, 0, x_516);
lean_closure_set(x_569, 1, x_518);
lean_closure_set(x_569, 2, x_1);
lean_closure_set(x_569, 3, x_568);
x_570 = lean_box(0);
x_571 = lean_box(0);
x_572 = lean_box(1);
x_573 = lean_box(x_513);
x_574 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lam__2___boxed), 2, 1);
lean_closure_set(x_574, 0, x_573);
x_575 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_575, 0, x_562);
lean_ctor_set(x_575, 1, x_546);
lean_ctor_set(x_575, 2, x_524);
lean_ctor_set(x_575, 3, x_524);
lean_ctor_set_usize(x_575, 4, x_527);
x_576 = lean_box(0);
x_577 = lean_box(0);
x_578 = lean_box(0);
x_579 = lean_box(0);
x_580 = lean_box(0);
x_581 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_581, 0, x_513);
lean_ctor_set_uint8(x_581, 1, x_513);
lean_ctor_set_uint8(x_581, 2, x_513);
lean_ctor_set_uint8(x_581, 3, x_513);
lean_ctor_set_uint8(x_581, 4, x_513);
x_582 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 5, x_582);
x_583 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 6, x_583);
lean_ctor_set_uint8(x_581, 7, x_513);
x_584 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 8, x_584);
x_585 = lean_unbox(x_563);
lean_ctor_set_uint8(x_581, 9, x_585);
x_586 = lean_unbox(x_564);
lean_ctor_set_uint8(x_581, 10, x_586);
x_587 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 11, x_587);
x_588 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 12, x_588);
x_589 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 13, x_589);
x_590 = lean_unbox(x_565);
lean_ctor_set_uint8(x_581, 14, x_590);
x_591 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 15, x_591);
x_592 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 16, x_592);
x_593 = lean_unbox(x_572);
lean_ctor_set_uint8(x_581, 17, x_593);
x_594 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_581);
x_595 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_595, 0, x_566);
lean_ctor_set(x_595, 1, x_567);
lean_ctor_set(x_595, 2, x_532);
x_596 = lean_mk_empty_array_with_capacity(x_524);
x_597 = lean_box(0);
x_598 = lean_box(0);
x_599 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed), 9, 2);
lean_closure_set(x_599, 0, lean_box(0));
lean_closure_set(x_599, 1, x_569);
x_600 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_600, 0, x_570);
lean_ctor_set(x_600, 1, x_571);
lean_ctor_set(x_600, 2, x_575);
lean_ctor_set(x_600, 3, x_574);
lean_ctor_set(x_600, 4, x_532);
lean_ctor_set(x_600, 5, x_532);
lean_ctor_set(x_600, 6, x_576);
x_601 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7, x_601);
x_602 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 1, x_602);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 2, x_513);
x_603 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 3, x_603);
x_604 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 4, x_604);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 5, x_513);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 6, x_513);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 7, x_513);
x_605 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 8, x_605);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 9, x_513);
x_606 = lean_unbox(x_572);
lean_ctor_set_uint8(x_600, sizeof(void*)*7 + 10, x_606);
x_607 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_607, 0, x_577);
lean_ctor_set(x_607, 1, x_532);
lean_ctor_set(x_607, 2, x_577);
lean_ctor_set(x_607, 3, x_578);
lean_ctor_set(x_607, 4, x_579);
lean_ctor_set(x_607, 5, x_532);
lean_ctor_set(x_607, 6, x_580);
x_608 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_608, 0, x_581);
lean_ctor_set(x_608, 1, x_532);
lean_ctor_set(x_608, 2, x_595);
lean_ctor_set(x_608, 3, x_596);
lean_ctor_set(x_608, 4, x_597);
lean_ctor_set(x_608, 5, x_524);
lean_ctor_set(x_608, 6, x_598);
lean_ctor_set_uint64(x_608, sizeof(void*)*7, x_594);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 8, x_513);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 9, x_513);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 10, x_513);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_553);
x_609 = l_Lean_Elab_Term_TermElabM_run___redArg(x_599, x_600, x_607, x_608, x_553, x_2, x_3, x_554);
lean_dec(x_608);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_st_ref_get(x_553, x_611);
lean_dec(x_553);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
x_615 = lean_mk_string_unchecked("_rpc_wrapped", 12, 12);
x_616 = l_Lean_Name_mkStr1(x_615);
lean_inc(x_1);
x_617 = l_Lean_Name_append(x_1, x_616);
x_618 = lean_ctor_get(x_610, 0);
lean_inc(x_618);
lean_dec(x_610);
lean_inc(x_617);
x_619 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_577);
lean_ctor_set(x_619, 2, x_568);
x_620 = lean_box(0);
x_621 = lean_box(1);
lean_inc(x_617);
if (lean_is_scalar(x_614)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_614;
 lean_ctor_set_tag(x_622, 1);
}
lean_ctor_set(x_622, 0, x_617);
lean_ctor_set(x_622, 1, x_577);
x_623 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_623, 0, x_619);
lean_ctor_set(x_623, 1, x_618);
lean_ctor_set(x_623, 2, x_620);
lean_ctor_set(x_623, 3, x_622);
x_624 = lean_unbox(x_621);
lean_ctor_set_uint8(x_623, sizeof(void*)*4, x_624);
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_623);
lean_inc(x_3);
lean_inc(x_2);
x_626 = l_Lean_addAndCompile(x_625, x_2, x_3, x_613);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_627 = lean_ctor_get(x_626, 1);
lean_inc(x_627);
lean_dec(x_626);
x_628 = lean_st_ref_get(x_3, x_627);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec(x_628);
x_631 = l_Lean_Server_registerRpcProcedure___lam__0(x_629, x_2, x_3, x_630);
lean_dec(x_2);
lean_dec(x_629);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_512, x_632, x_1, x_617);
x_635 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_634, x_3, x_633);
lean_dec(x_3);
return x_635;
}
else
{
lean_dec(x_617);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_626;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_568);
lean_dec(x_553);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_636 = lean_ctor_get(x_609, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_609, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_638 = x_609;
} else {
 lean_dec_ref(x_609);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_1);
x_640 = lean_mk_string_unchecked("", 0, 0);
x_641 = l_Lean_stringToMessageData(x_640);
lean_dec(x_640);
x_642 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_510);
x_643 = lean_mk_string_unchecked(": already registered", 20, 20);
x_644 = l_Lean_stringToMessageData(x_643);
lean_dec(x_643);
x_645 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_644);
x_646 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_645, x_2, x_3, x_502);
lean_dec(x_3);
lean_dec(x_2);
return x_646;
}
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_495);
lean_dec(x_1);
x_647 = lean_mk_string_unchecked("", 0, 0);
x_648 = l_Lean_stringToMessageData(x_647);
lean_dec(x_647);
x_649 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_510);
x_650 = lean_mk_string_unchecked(": already registered (builtin)", 30, 30);
x_651 = l_Lean_stringToMessageData(x_650);
lean_dec(x_650);
x_652 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_651);
x_653 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_652, x_2, x_3, x_502);
lean_dec(x_3);
lean_dec(x_2);
return x_653;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Server_registerRpcProcedure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerRpcProcedure___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Server_registerRpcProcedure___lam__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_registerRpcProcedure(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Server", 6, 6);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_5);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = lean_mk_string_unchecked("Rpc", 3, 3);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("RequestHandling", 15, 15);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(1450u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("server_rpc_method", 17, 17);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("Marks a function as a Lean server RPC method.\n    Shorthand for `registerRpcProcedure`.\n    The function must have type `α → RequestM (RequestTask β)` with\n    `[RpcEncodable α]` and `[RpcEncodable β]`.", 208, 202);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_3);
x_30 = l_Lean_registerBuiltinAttribute(x_29, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Server_initFn___lam__0____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_initFn___lam__1____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedRpcProcedure = _init_l_Lean_Server_instInhabitedRpcProcedure();
lean_mark_persistent(l_Lean_Server_instInhabitedRpcProcedure);
if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_33_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_builtinRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_builtinRpcProcedures);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_76_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_userRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_userRpcProcedures);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1450_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
