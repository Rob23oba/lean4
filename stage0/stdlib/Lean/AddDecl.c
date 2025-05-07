// Lean compiler output
// Module: Lean.AddDecl
// Imports: Lean.CoreM Lean.Namespace Lean.Util.CollectAxioms
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addDecl___lam__1(uint8_t, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_addDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isSimpleRflProof___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
extern lean_object* l_Lean_debug_skipKernelTC;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_addDecl_addSynchronously_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_async;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
uint8_t l_Lean_Declaration_hasSorry(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_wasOriginallyTheorem___boxed(lean_object*, lean_object*);
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType(lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isSimpleRflProof(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_addSynchronously(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242____boxed(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_privateConstKindsExt;
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AddDecl___hyg_242_(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_debug_skipKernelTC;
x_6 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; lean_object* x_9; 
x_7 = l_Lean_Core_getMaxHeartbeats(x_2);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_add_decl(x_1, x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_add_decl_without_checking(x_1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Kernel_Environment_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Core_getMaxHeartbeats(x_2);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = l_Lean_debug_skipKernelTC;
x_8 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Environment_addDeclCore(x_1, x_6, x_3, x_4, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Environment_addDeclCore(x_1, x_6, x_3, x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
x_1 = x_2;
goto _start;
}
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_AddDecl_0__Lean_isNamespaceName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l___private_Lean_AddDecl_0__Lean_isNamespaceName(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Environment_registerNamespace(x_1, x_3);
x_1 = x_5;
x_2 = x_3;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_get(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(95u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(x_1, x_2);
return x_9;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AddDecl___hyg_242_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("_private", 8, 8);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("AddDecl", 7, 7);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Name_num___override(x_9, x_10);
x_12 = l_Lean_Name_str___override(x_11, x_6);
x_13 = lean_mk_string_unchecked("privateConstKindsExt", 20, 20);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_mkMapDeclarationExtension___redArg(x_14, x_2, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn___lam__0____x40_Lean_AddDecl___hyg_242_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getOriginalConstKind_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = l___private_Lean_AddDecl_0__Lean_privateConstKindsExt;
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_3, x_4, x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Environment_setExporting(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unbox(x_5);
x_11 = l_Lean_Environment_findAsync_x3f(x_9, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
return x_7;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_15 = lean_box(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
lean_dec(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_wasOriginallyTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOriginalConstKind_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_wasOriginallyTheorem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_wasOriginallyTheorem(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isSimpleRflProof(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("rfl", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isSimpleRflProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_AddDecl_0__Lean_isSimpleRflProof(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("WellFounded", 11, 11);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_interruptExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Kernel_Exception_toMessageData(x_1, x_6);
x_8 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 16)
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___redArg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("sorryAx", 7, 7);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Level_ofNat(x_27);
x_29 = lean_box(0);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_28);
x_30 = l_Lean_Expr_const___override(x_26, x_1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Level_ofNat(x_31);
x_33 = l_Lean_Expr_sort___override(x_32);
x_34 = lean_mk_string_unchecked("Bool", 4, 4);
x_35 = lean_mk_string_unchecked("true", 4, 4);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = l_Lean_Expr_const___override(x_36, x_29);
x_38 = l_Lean_mkAppB(x_30, x_33, x_37);
x_39 = lean_st_ref_get(x_4, x_5);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_24);
lean_ctor_set(x_42, 2, x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 11);
lean_inc(x_49);
x_50 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_47, x_48, x_46, x_49);
lean_dec(x_49);
lean_dec(x_48);
lean_inc(x_3);
x_51 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_50, x_3, x_4, x_41);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_53, x_4, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_51, 1, x_11);
lean_ctor_set(x_51, 0, x_58);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_51, 1, x_11);
lean_ctor_set(x_51, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_62, x_4, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_11);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_11);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_dec(x_51);
x_19 = x_70;
x_20 = x_71;
goto block_23;
}
block_18:
{
if (x_15 == 0)
{
lean_dec(x_14);
x_1 = x_9;
x_2 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
block_23:
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
x_13 = x_20;
x_14 = x_19;
x_15 = x_22;
goto block_18;
}
else
{
x_13 = x_20;
x_14 = x_19;
x_15 = x_21;
goto block_18;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_88 = lean_box(0);
x_89 = lean_mk_string_unchecked("sorryAx", 7, 7);
x_90 = l_Lean_Name_mkStr1(x_89);
x_91 = lean_unsigned_to_nat(1u);
x_92 = l_Lean_Level_ofNat(x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Expr_const___override(x_90, x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_Level_ofNat(x_96);
x_98 = l_Lean_Expr_sort___override(x_97);
x_99 = lean_mk_string_unchecked("Bool", 4, 4);
x_100 = lean_mk_string_unchecked("true", 4, 4);
x_101 = l_Lean_Name_mkStr2(x_99, x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_93);
x_103 = l_Lean_mkAppB(x_95, x_98, x_102);
x_104 = lean_st_ref_get(x_4, x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_72);
lean_ctor_set(x_107, 1, x_88);
lean_ctor_set(x_107, 2, x_103);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_109);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_ctor_get(x_3, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 11);
lean_inc(x_114);
x_115 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_112, x_113, x_111, x_114);
lean_dec(x_114);
lean_dec(x_113);
lean_inc(x_3);
x_116 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_115, x_3, x_4, x_106);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_117, x_4, x_118);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_75);
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_75);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_116, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_dec(x_116);
x_83 = x_126;
x_84 = x_127;
goto block_87;
}
block_82:
{
if (x_79 == 0)
{
lean_dec(x_78);
x_1 = x_73;
x_2 = x_76;
x_5 = x_77;
goto _start;
}
else
{
lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_3);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
block_87:
{
uint8_t x_85; 
x_85 = l_Lean_Exception_isInterrupt(x_83);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Exception_isRuntime(x_83);
x_77 = x_84;
x_78 = x_83;
x_79 = x_86;
goto block_82;
}
else
{
x_77 = x_84;
x_78 = x_83;
x_79 = x_85;
goto block_82;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_addAsAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_st_ref_get(x_3, x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 11);
lean_inc(x_51);
x_52 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_49, x_50, x_48, x_51);
lean_dec(x_51);
lean_dec(x_50);
lean_inc(x_2);
x_53 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_52, x_2, x_3, x_43);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_54, x_3, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_dec(x_53);
x_65 = l_Lean_Exception_isInterrupt(x_63);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Exception_isRuntime(x_63);
x_30 = x_63;
x_31 = x_64;
x_32 = x_66;
goto block_34;
}
else
{
x_30 = x_63;
x_31 = x_64;
x_32 = x_65;
goto block_34;
}
}
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_st_ref_get(x_3, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_unbox(x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec(x_69);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 11);
lean_inc(x_78);
x_79 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_76, x_77, x_75, x_78);
lean_dec(x_78);
lean_dec(x_77);
lean_inc(x_2);
x_80 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_79, x_2, x_3, x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_81, x_3, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_83, 0, x_86);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_80, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
x_92 = l_Lean_Exception_isInterrupt(x_90);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Exception_isRuntime(x_90);
x_35 = x_91;
x_36 = x_90;
x_37 = x_93;
goto block_39;
}
else
{
x_35 = x_91;
x_36 = x_90;
x_37 = x_92;
goto block_39;
}
}
}
default: 
{
x_5 = x_2;
x_6 = x_3;
x_7 = x_4;
goto block_29;
}
}
block_29:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Declaration_getNames(x_1);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg(x_8, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
block_34:
{
if (x_32 == 0)
{
lean_dec(x_30);
x_5 = x_2;
x_6 = x_3;
x_7 = x_31;
goto block_29;
}
else
{
lean_object* x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
block_39:
{
if (x_37 == 0)
{
lean_dec(x_36);
x_5 = x_2;
x_6 = x_3;
x_7 = x_35;
goto block_29;
}
else
{
lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_addDecl_addAsAxiom_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_addAsAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDecl_addAsAxiom(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_warningAsError;
x_7 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_9, x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(2);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_12, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("typechecking declarations ", 26, 26);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = l_Lean_Declaration_getTopLevelNames(x_1);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_8, x_9);
x_11 = l_Lean_MessageData_ofList(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_get(x_3, x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_44, 5);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_MessageLog_hasErrors(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Declaration_hasSorry(x_1);
if (x_48 == 0)
{
lean_free_object(x_42);
x_17 = x_2;
x_18 = x_3;
x_19 = x_45;
goto block_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_mk_string_unchecked("hasSorry", 8, 8);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = lean_mk_string_unchecked("declaration uses 'sorry'", 24, 24);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
lean_ctor_set_tag(x_42, 8);
lean_ctor_set(x_42, 1, x_52);
lean_ctor_set(x_42, 0, x_50);
lean_inc(x_2);
x_53 = l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0(x_42, x_2, x_3, x_45);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_17 = x_2;
x_18 = x_3;
x_19 = x_54;
goto block_41;
}
}
else
{
lean_free_object(x_42);
x_17 = x_2;
x_18 = x_3;
x_19 = x_45;
goto block_41;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_57 = lean_ctor_get(x_55, 5);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_MessageLog_hasErrors(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Declaration_hasSorry(x_1);
if (x_59 == 0)
{
x_17 = x_2;
x_18 = x_3;
x_19 = x_56;
goto block_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_mk_string_unchecked("hasSorry", 8, 8);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = lean_mk_string_unchecked("declaration uses 'sorry'", 24, 24);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_2);
x_65 = l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0(x_64, x_2, x_3, x_56);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_17 = x_2;
x_18 = x_3;
x_19 = x_66;
goto block_41;
}
}
else
{
x_17 = x_2;
x_18 = x_3;
x_19 = x_56;
goto block_41;
}
}
block_16:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = l_Lean_addDecl_addAsAxiom(x_1, x_5, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_dec(x_8);
return x_11;
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
block_41:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_st_ref_get(x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 11);
lean_inc(x_25);
lean_inc(x_1);
x_26 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_23, x_24, x_1, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_inc(x_17);
x_27 = l_Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0___redArg(x_26, x_17, x_18, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_28, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
x_34 = l_Lean_Exception_isInterrupt(x_32);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_32);
x_5 = x_17;
x_6 = x_33;
x_7 = x_27;
x_8 = x_32;
x_9 = x_18;
x_10 = x_35;
goto block_16;
}
else
{
x_5 = x_17;
x_6 = x_33;
x_7 = x_27;
x_8 = x_32;
x_9 = x_18;
x_10 = x_34;
goto block_16;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Exception_isInterrupt(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Exception_isRuntime(x_36);
x_5 = x_17;
x_6 = x_37;
x_7 = x_38;
x_8 = x_36;
x_9 = x_18;
x_10 = x_40;
goto block_16;
}
else
{
x_5 = x_17;
x_6 = x_37;
x_7 = x_38;
x_8 = x_36;
x_9 = x_18;
x_10 = x_39;
goto block_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_addDecl_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_addDecl_doAdd___lam__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_mk_string_unchecked("type checking", 13, 13);
x_9 = lean_mk_string_unchecked("Kernel", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_box(1);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed), 9, 6);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_8, x_7, x_13, x_14, x_2, x_3, x_4);
lean_dec(x_7);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at___Lean_addDecl_doAdd_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDecl_doAdd___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDecl_doAdd___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_addDecl_addSynchronously_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_st_ref_get(x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_task_get_own(x_15);
lean_inc(x_7);
x_17 = lean_environment_find(x_16, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
x_18 = lean_mk_string_unchecked("Lean.AddDecl", 12, 12);
x_19 = lean_mk_string_unchecked("Lean.addDecl.addSynchronously", 29, 29);
x_20 = lean_unsigned_to_nat(135u);
x_21 = lean_unsigned_to_nat(49u);
x_22 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_23 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_panic___at___Lean_addDecl_addSynchronously_spec__0(x_23, x_3, x_4, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_1 = x_8;
x_2 = x_13;
x_5 = x_25;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
x_28 = l_Lean_ConstantKind_ofConstantInfo(x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_31 = lean_unbox(x_29);
x_32 = lean_unbox(x_30);
lean_inc(x_14);
x_33 = l_Lean_Environment_addConstAsync(x_14, x_7, x_28, x_28, x_31, x_32, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
lean_inc(x_17);
lean_inc(x_34);
x_37 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_34, x_14, x_17, x_36, x_35);
lean_dec(x_14);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_17, 0);
lean_dec(x_39);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_34);
x_42 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_34, x_41, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_17);
lean_free_object(x_9);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_44, x_4, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_1 = x_8;
x_2 = x_13;
x_5 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_io_error_to_string(x_49);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_51);
x_52 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_52);
lean_ctor_set(x_9, 0, x_50);
lean_ctor_set(x_42, 0, x_9);
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_ctor_get(x_3, 5);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_io_error_to_string(x_53);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_56);
x_57 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_57);
lean_ctor_set(x_9, 0, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_9);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_37);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_3, 5);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_io_error_to_string(x_60);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_62);
x_63 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_63);
lean_ctor_set(x_9, 0, x_61);
lean_ctor_set(x_37, 0, x_9);
return x_37;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
x_66 = lean_ctor_get(x_3, 5);
lean_inc(x_66);
lean_dec(x_3);
x_67 = lean_io_error_to_string(x_64);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_67);
x_68 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_68);
lean_ctor_set(x_9, 0, x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
else
{
lean_dec(x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_dec(x_37);
x_71 = lean_ctor_get(x_34, 1);
lean_inc(x_71);
lean_inc(x_34);
x_72 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_34, x_71, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_9);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get(x_34, 0);
lean_inc(x_74);
lean_dec(x_34);
x_75 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_74, x_4, x_73);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_1 = x_8;
x_2 = x_13;
x_5 = x_76;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_4);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_3, 5);
lean_inc(x_81);
lean_dec(x_3);
x_82 = lean_io_error_to_string(x_78);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_MessageData_ofFormat(x_83);
lean_ctor_set(x_9, 1, x_84);
lean_ctor_set(x_9, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_9);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_4);
x_86 = lean_ctor_get(x_37, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_37, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_88 = x_37;
} else {
 lean_dec_ref(x_37);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_3, 5);
lean_inc(x_89);
lean_dec(x_3);
x_90 = lean_io_error_to_string(x_86);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
lean_ctor_set(x_9, 1, x_92);
lean_ctor_set(x_9, 0, x_89);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_9);
lean_ctor_set(x_93, 1, x_87);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_17);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_17, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_33);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_33, 0);
x_98 = lean_ctor_get(x_3, 5);
lean_inc(x_98);
lean_dec(x_3);
x_99 = lean_io_error_to_string(x_97);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_99);
x_100 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_100);
lean_ctor_set(x_9, 0, x_98);
lean_ctor_set(x_33, 0, x_9);
return x_33;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_33, 0);
x_102 = lean_ctor_get(x_33, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_33);
x_103 = lean_ctor_get(x_3, 5);
lean_inc(x_103);
lean_dec(x_3);
x_104 = lean_io_error_to_string(x_101);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_104);
x_105 = l_Lean_MessageData_ofFormat(x_17);
lean_ctor_set(x_9, 1, x_105);
lean_ctor_set(x_9, 0, x_103);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_9);
lean_ctor_set(x_106, 1, x_102);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_17);
x_107 = lean_ctor_get(x_33, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_33, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_109 = x_33;
} else {
 lean_dec_ref(x_33);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_3, 5);
lean_inc(x_110);
lean_dec(x_3);
x_111 = lean_io_error_to_string(x_107);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
lean_ctor_set(x_9, 1, x_113);
lean_ctor_set(x_9, 0, x_110);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_9);
lean_ctor_set(x_114, 1, x_108);
return x_114;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_9, 0);
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_9);
x_117 = lean_box(0);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
x_120 = lean_task_get_own(x_119);
lean_inc(x_7);
x_121 = lean_environment_find(x_120, x_7);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_118);
lean_dec(x_7);
x_122 = lean_mk_string_unchecked("Lean.AddDecl", 12, 12);
x_123 = lean_mk_string_unchecked("Lean.addDecl.addSynchronously", 29, 29);
x_124 = lean_unsigned_to_nat(135u);
x_125 = lean_unsigned_to_nat(49u);
x_126 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_127 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_122, x_123, x_124, x_125, x_126);
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_122);
lean_inc(x_4);
lean_inc(x_3);
x_128 = l_panic___at___Lean_addDecl_addSynchronously_spec__0(x_127, x_3, x_4, x_116);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_1 = x_8;
x_2 = x_117;
x_5 = x_129;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_128;
}
}
else
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
x_132 = l_Lean_ConstantKind_ofConstantInfo(x_131);
lean_dec(x_131);
x_133 = lean_box(0);
x_134 = lean_box(1);
x_135 = lean_unbox(x_133);
x_136 = lean_unbox(x_134);
lean_inc(x_118);
x_137 = l_Lean_Environment_addConstAsync(x_118, x_7, x_132, x_132, x_135, x_136, x_116);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_box(0);
lean_inc(x_121);
lean_inc(x_138);
x_141 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_138, x_118, x_121, x_140, x_139);
lean_dec(x_118);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_142 = x_121;
} else {
 lean_dec_ref(x_121);
 x_142 = lean_box(0);
}
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_inc(x_138);
x_145 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_138, x_144, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
lean_dec(x_138);
x_148 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_147, x_4, x_146);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_1 = x_8;
x_2 = x_117;
x_5 = x_149;
goto _start;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_4);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_153 = x_145;
} else {
 lean_dec_ref(x_145);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_3, 5);
lean_inc(x_154);
lean_dec(x_3);
x_155 = lean_io_error_to_string(x_151);
if (lean_is_scalar(x_142)) {
 x_156 = lean_alloc_ctor(3, 1, 0);
} else {
 x_156 = x_142;
 lean_ctor_set_tag(x_156, 3);
}
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_MessageData_ofFormat(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_4);
x_160 = lean_ctor_get(x_141, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_141, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_162 = x_141;
} else {
 lean_dec_ref(x_141);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_3, 5);
lean_inc(x_163);
lean_dec(x_3);
x_164 = lean_io_error_to_string(x_160);
if (lean_is_scalar(x_142)) {
 x_165 = lean_alloc_ctor(3, 1, 0);
} else {
 x_165 = x_142;
 lean_ctor_set_tag(x_165, 3);
}
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_MessageData_ofFormat(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
if (lean_is_scalar(x_162)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_162;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_161);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_118);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_169 = x_121;
} else {
 lean_dec_ref(x_121);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_137, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_137, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_172 = x_137;
} else {
 lean_dec_ref(x_137);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_3, 5);
lean_inc(x_173);
lean_dec(x_3);
x_174 = lean_io_error_to_string(x_170);
if (lean_is_scalar(x_169)) {
 x_175 = lean_alloc_ctor(3, 1, 0);
} else {
 x_175 = x_169;
 lean_ctor_set_tag(x_175, 3);
}
lean_ctor_set(x_175, 0, x_174);
x_176 = l_Lean_MessageData_ofFormat(x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_172)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_172;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_171);
return x_178;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_addSynchronously(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_addDecl_doAdd(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Declaration_getNames(x_1);
x_8 = lean_box(0);
x_9 = l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___redArg(x_7, x_8, x_2, x_3, x_6);
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
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_addDecl_addSynchronously_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_addDecl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_Lean_addDecl___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_addDecl_doAdd(x_2, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_7, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_6);
x_18 = lean_apply_4(x_3, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_4, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_free_object(x_14);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_6, 5);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_io_error_to_string(x_27);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_28);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_io_error_to_string(x_32);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
lean_ctor_set(x_14, 1, x_37);
lean_ctor_set(x_14, 0, x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
lean_inc(x_6);
x_45 = lean_apply_4(x_3, x_43, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_4, x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_12);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_6, 5);
lean_inc(x_55);
lean_dec(x_6);
x_56 = lean_io_error_to_string(x_52);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_11, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_st_ref_get(x_7, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_6);
x_71 = lean_apply_4(x_3, x_69, x_6, x_7, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_4, x_72, x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_free_object(x_67);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_65);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_6, 5);
lean_inc(x_81);
lean_dec(x_6);
x_82 = lean_io_error_to_string(x_80);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_MessageData_ofFormat(x_83);
lean_ctor_set(x_67, 1, x_84);
lean_ctor_set(x_67, 0, x_81);
lean_ctor_set(x_74, 0, x_67);
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_87 = lean_ctor_get(x_6, 5);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_io_error_to_string(x_85);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_MessageData_ofFormat(x_89);
lean_ctor_set(x_67, 1, x_90);
lean_ctor_set(x_67, 0, x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_67);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_4);
x_92 = !lean_is_exclusive(x_71);
if (x_92 == 0)
{
return x_71;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_71, 0);
x_94 = lean_ctor_get(x_71, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_71);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_67, 0);
x_97 = lean_ctor_get(x_67, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_67);
lean_inc(x_6);
x_98 = lean_apply_4(x_3, x_96, x_6, x_7, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_4, x_99, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_6);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
 lean_ctor_set_tag(x_104, 1);
}
lean_ctor_set(x_104, 0, x_65);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_65);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_6, 5);
lean_inc(x_108);
lean_dec(x_6);
x_109 = lean_io_error_to_string(x_105);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = l_Lean_MessageData_ofFormat(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_107)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_107;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_4);
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_116 = x_98;
} else {
 lean_dec_ref(x_98);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
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
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_6);
x_109 = x_10;
x_110 = x_11;
x_111 = x_12;
goto block_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_128 = lean_st_ref_take(x_11, x_12);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = l___private_Lean_AddDecl_0__Lean_privateConstKindsExt;
lean_inc(x_26);
lean_inc(x_24);
x_133 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_132, x_131, x_24, x_26);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 7);
lean_inc(x_139);
lean_dec(x_129);
x_140 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_140, 2, x_135);
lean_ctor_set(x_140, 3, x_136);
lean_ctor_set(x_140, 4, x_6);
lean_ctor_set(x_140, 5, x_137);
lean_ctor_set(x_140, 6, x_138);
lean_ctor_set(x_140, 7, x_139);
x_141 = lean_st_ref_set(x_11, x_140, x_130);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_109 = x_10;
x_110 = x_11;
x_111 = x_142;
goto block_127;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_16);
x_21 = l_Lean_Core_logSnapshotTask(x_20, x_14, x_15, x_13);
lean_dec(x_15);
lean_dec(x_14);
return x_21;
}
block_108:
{
uint8_t x_33; lean_object* x_34; 
x_33 = lean_unbox(x_26);
lean_dec(x_26);
lean_inc(x_28);
x_34 = l_Lean_Environment_addConstAsync(x_28, x_24, x_33, x_32, x_1, x_2, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_25);
lean_inc(x_35);
x_39 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_35, x_37, x_38, x_7, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_27);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_41, x_31, x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_IO_CancelToken_new(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_addDecl___lam__2___boxed), 8, 4);
lean_closure_set(x_47, 0, x_37);
lean_closure_set(x_47, 1, x_3);
lean_closure_set(x_47, 2, x_4);
lean_closure_set(x_47, 3, x_35);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("addDecl", 7, 7);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = l_Lean_Name_toString(x_51, x_2, x_5);
lean_inc(x_30);
lean_inc(x_48);
x_53 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_47, x_48, x_52, x_30, x_31, x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_28, 2);
lean_inc(x_56);
lean_dec(x_28);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_io_map_task(x_54, x_56, x_57, x_1, x_55);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_30, 5);
lean_inc(x_62);
x_63 = l_Lean_Syntax_getTailPos_x3f(x_62, x_1);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_free_object(x_58);
x_64 = lean_box(0);
x_13 = x_61;
x_14 = x_30;
x_15 = x_31;
x_16 = x_60;
x_17 = x_48;
x_18 = x_64;
goto block_22;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_ctor_set(x_58, 1, x_66);
lean_ctor_set(x_58, 0, x_66);
lean_ctor_set(x_63, 0, x_58);
x_13 = x_61;
x_14 = x_30;
x_15 = x_31;
x_16 = x_60;
x_17 = x_48;
x_18 = x_63;
goto block_22;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
lean_inc(x_67);
lean_ctor_set(x_58, 1, x_67);
lean_ctor_set(x_58, 0, x_67);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_58);
x_13 = x_61;
x_14 = x_30;
x_15 = x_31;
x_16 = x_60;
x_17 = x_48;
x_18 = x_68;
goto block_22;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_30, 5);
lean_inc(x_71);
x_72 = l_Lean_Syntax_getTailPos_x3f(x_71, x_1);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_13 = x_70;
x_14 = x_30;
x_15 = x_31;
x_16 = x_69;
x_17 = x_48;
x_18 = x_73;
goto block_22;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
lean_inc(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_74);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
x_13 = x_70;
x_14 = x_30;
x_15 = x_31;
x_16 = x_69;
x_17 = x_48;
x_18 = x_77;
goto block_22;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_39);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_39, 0);
x_80 = lean_ctor_get(x_30, 5);
lean_inc(x_80);
lean_dec(x_30);
x_81 = lean_io_error_to_string(x_79);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
if (lean_is_scalar(x_27)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_27;
}
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_39, 0, x_84);
return x_39;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_39, 0);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_39);
x_87 = lean_ctor_get(x_30, 5);
lean_inc(x_87);
lean_dec(x_30);
x_88 = lean_io_error_to_string(x_85);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_MessageData_ofFormat(x_89);
if (lean_is_scalar(x_27)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_27;
}
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_34);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_30, 5);
lean_inc(x_95);
lean_dec(x_30);
x_96 = lean_io_error_to_string(x_94);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_MessageData_ofFormat(x_97);
if (lean_is_scalar(x_27)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_27;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_34, 0, x_99);
return x_34;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_34, 0);
x_101 = lean_ctor_get(x_34, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_34);
x_102 = lean_ctor_get(x_30, 5);
lean_inc(x_102);
lean_dec(x_30);
x_103 = lean_io_error_to_string(x_100);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_MessageData_ofFormat(x_104);
if (lean_is_scalar(x_27)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_27;
}
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_101);
return x_107;
}
}
}
block_127:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_st_ref_get(x_110, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_4);
lean_inc(x_110);
lean_inc(x_109);
x_115 = lean_apply_4(x_4, x_113, x_109, x_110, x_114);
if (lean_obj_tag(x_115) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unbox(x_26);
x_28 = x_116;
x_29 = x_117;
x_30 = x_109;
x_31 = x_110;
x_32 = x_118;
goto block_108;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_ctor_get(x_8, 0);
lean_inc(x_121);
lean_dec(x_8);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
x_28 = x_119;
x_29 = x_120;
x_30 = x_109;
x_31 = x_110;
x_32 = x_122;
goto block_108;
}
}
else
{
uint8_t x_123; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
return x_115;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_115, 0);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_115);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_Declaration_getNames(x_1);
x_11 = l_List_foldl___at___Lean_addDecl_spec__0(x_9, x_10);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_16);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_ctor_get(x_7, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 7);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_5);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_5);
lean_ctor_set(x_20, 5, x_17);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = l_Lean_Elab_async;
x_26 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_5);
x_27 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 4, 0);
x_29 = lean_box(0);
x_30 = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_23);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_50 = lean_box(2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unbox(x_29);
x_54 = l_Lean_addDecl___lam__3(x_53, x_26, x_1, x_28, x_30, x_5, x_31, x_32, x_52, x_2, x_3, x_22);
return x_54;
}
case 1:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_33 = x_55;
x_34 = x_2;
x_35 = x_3;
x_36 = x_22;
goto block_45;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_74; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_23);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_st_ref_get(x_3, x_22);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_85 = lean_ctor_get(x_58, 0);
lean_inc(x_85);
lean_dec(x_58);
x_86 = l_Lean_Environment_header(x_85);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*5 + 4);
lean_dec(x_86);
if (x_87 == 0)
{
x_74 = x_87;
goto block_84;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_56, 1);
lean_inc(x_88);
x_89 = l___private_Lean_AddDecl_0__Lean_isSimpleRflProof(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
x_74 = x_87;
goto block_84;
}
else
{
x_61 = x_31;
x_62 = x_32;
x_63 = x_2;
x_64 = x_3;
goto block_73;
}
}
block_73:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_56);
x_68 = lean_box(1);
if (lean_is_scalar(x_60)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_60;
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_unbox(x_29);
x_72 = l_Lean_addDecl___lam__3(x_71, x_26, x_1, x_28, x_30, x_5, x_61, x_62, x_70, x_63, x_64, x_59);
return x_72;
}
block_84:
{
if (x_74 == 0)
{
x_61 = x_31;
x_62 = x_32;
x_63 = x_2;
x_64 = x_3;
goto block_73;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_77 = l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_75);
x_79 = lean_unbox(x_29);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_box(2);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_61 = x_81;
x_62 = x_83;
x_63 = x_2;
x_64 = x_3;
goto block_73;
}
else
{
lean_dec(x_75);
x_61 = x_31;
x_62 = x_32;
x_63 = x_2;
x_64 = x_3;
goto block_73;
}
}
}
}
case 5:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_5);
x_91 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_22);
return x_91;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_33 = x_93;
x_34 = x_2;
x_35 = x_3;
x_36 = x_22;
goto block_45;
}
else
{
lean_object* x_94; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_5);
x_94 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_22);
return x_94;
}
}
}
default: 
{
lean_object* x_95; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_5);
x_95 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_22);
return x_95;
}
}
block_45:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_40 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_23;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unbox(x_29);
x_44 = l_Lean_addDecl___lam__3(x_43, x_26, x_1, x_28, x_30, x_5, x_31, x_32, x_42, x_34, x_35, x_36);
return x_44;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_96 = lean_ctor_get(x_5, 0);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_5);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_inc(x_1);
x_99 = l_Lean_Declaration_getNames(x_1);
x_100 = l_List_foldl___at___Lean_addDecl_spec__0(x_98, x_99);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 3);
lean_inc(x_103);
x_104 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_inc(x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_ctor_get(x_96, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_96, 6);
lean_inc(x_108);
x_109 = lean_ctor_get(x_96, 7);
lean_inc(x_109);
lean_dec(x_96);
lean_inc(x_106);
x_110 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_102);
lean_ctor_set(x_110, 3, x_103);
lean_ctor_set(x_110, 4, x_106);
lean_ctor_set(x_110, 5, x_107);
lean_ctor_set(x_110, 6, x_108);
lean_ctor_set(x_110, 7, x_109);
x_111 = lean_st_ref_set(x_3, x_110, x_97);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
x_115 = l_Lean_Elab_async;
x_116 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_114, x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_113);
lean_dec(x_106);
x_117 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_112);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_alloc_closure((void*)(l_Lean_addDecl___lam__0___boxed), 4, 0);
x_119 = lean_box(0);
x_120 = lean_alloc_closure((void*)(l_Lean_addDecl___lam__1___boxed), 2, 1);
lean_closure_set(x_120, 0, x_119);
x_121 = lean_box(0);
x_122 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
lean_dec(x_113);
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_136);
x_140 = lean_box(2);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_unbox(x_119);
x_144 = l_Lean_addDecl___lam__3(x_143, x_116, x_1, x_118, x_120, x_106, x_121, x_122, x_142, x_2, x_3, x_112);
return x_144;
}
case 1:
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_123 = x_145;
x_124 = x_2;
x_125 = x_3;
x_126 = x_112;
goto block_135;
}
case 2:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_164; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_113);
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_st_ref_get(x_3, x_112);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_175 = lean_ctor_get(x_148, 0);
lean_inc(x_175);
lean_dec(x_148);
x_176 = l_Lean_Environment_header(x_175);
lean_dec(x_175);
x_177 = lean_ctor_get_uint8(x_176, sizeof(void*)*5 + 4);
lean_dec(x_176);
if (x_177 == 0)
{
x_164 = x_177;
goto block_174;
}
else
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_146, 1);
lean_inc(x_178);
x_179 = l___private_Lean_AddDecl_0__Lean_isSimpleRflProof(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
x_164 = x_177;
goto block_174;
}
else
{
x_151 = x_121;
x_152 = x_122;
x_153 = x_2;
x_154 = x_3;
goto block_163;
}
}
block_163:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_146, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_146);
x_158 = lean_box(1);
if (lean_is_scalar(x_150)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_150;
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_unbox(x_119);
x_162 = l_Lean_addDecl___lam__3(x_161, x_116, x_1, x_118, x_120, x_106, x_151, x_152, x_160, x_153, x_154, x_149);
return x_162;
}
block_174:
{
if (x_164 == 0)
{
x_151 = x_121;
x_152 = x_122;
x_153 = x_2;
x_154 = x_3;
goto block_163;
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_146, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 2);
lean_inc(x_166);
x_167 = l___private_Lean_AddDecl_0__Lean_looksLikeRelevantTheoremProofType(x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_165);
x_169 = lean_unbox(x_119);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_169);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_168);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_box(2);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_151 = x_171;
x_152 = x_173;
x_153 = x_2;
x_154 = x_3;
goto block_163;
}
else
{
lean_dec(x_165);
x_151 = x_121;
x_152 = x_122;
x_153 = x_2;
x_154 = x_3;
goto block_163;
}
}
}
}
case 5:
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_106);
x_181 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_112);
return x_181;
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
lean_dec(x_180);
x_123 = x_183;
x_124 = x_2;
x_125 = x_3;
x_126 = x_112;
goto block_135;
}
else
{
lean_object* x_184; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_106);
x_184 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_112);
return x_184;
}
}
}
default: 
{
lean_object* x_185; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_106);
x_185 = l_Lean_addDecl_addSynchronously(x_1, x_2, x_3, x_112);
return x_185;
}
}
block_135:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_123);
x_130 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_113;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_unbox(x_119);
x_134 = l_Lean_addDecl___lam__3(x_133, x_116, x_1, x_118, x_120, x_106, x_121, x_122, x_132, x_124, x_125, x_126);
return x_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDecl___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_addDecl___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addDecl___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_addDecl___lam__3(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_addDecl(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_compileDecl(x_1, x_8, x_2, x_3, x_6);
return x_9;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Namespace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectAxioms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_AddDecl___hyg_242_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_AddDecl_0__Lean_privateConstKindsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_AddDecl_0__Lean_privateConstKindsExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
