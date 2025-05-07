// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Lean.Util.CollectLevelParams Lean.Elab.DeclUtil Lean.Elab.DefView Lean.Elab.MutualDef Lean.Elab.MutualInductive Lean.Elab.DeclarationRange
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7438_(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_inductiveElabAttr;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Term_elabMutualDef_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0(lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_object*);
lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
lean_object* l_panic___at_____private_Lean_Elab_Do_0__Lean_Elab_Term_Do_destructTuple_destruct_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withoutCommandIncrementality___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0___boxed(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__2___boxed(lean_object**);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_elabAttrs___at___Lean_Elab_elabDeclAttrs___at___Lean_Elab_elabModifiers___at___Lean_Elab_Command_elabMutualInductive_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lam__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lam__0(uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___Lean_Elab_Command_elabMutualInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_object*);
lean_object* l_Lean_throwUnknownIdentifier___at___Lean_Elab_Term_resolveName_process_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicitForbiddenPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___boxed(lean_object*);
lean_object* l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_mk_string_unchecked("_root_", 6, 6);
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0___boxed), 1, 0);
x_12 = lean_mk_string_unchecked("invalid namespace '", 19, 19);
x_13 = l_Lean_Name_toString(x_1, x_9, x_11);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("', '_root_' is a reserved namespace", 35, 35);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lean_Macro_throwError___redArg(x_16, x_2, x_3);
return x_17;
}
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0___boxed), 1, 0);
x_19 = lean_mk_string_unchecked("invalid namespace '", 19, 19);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Name_toString(x_1, x_21, x_18);
x_23 = lean_string_append(x_19, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("', it must not contain numeric parts", 36, 36);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Lean_Macro_throwError___redArg(x_25, x_2, x_3);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Elab_expandDeclIdCore(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("_root_", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Name_isPrefixOf(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getHeadInfo(x_1);
x_9 = lean_mk_syntax_ident(x_2);
x_10 = l_Lean_Syntax_setInfo(x_8, x_9);
x_11 = l_Lean_Syntax_isIdent(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_setArg(x_1, x_12, x_10);
return x_13;
}
else
{
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Lean.Elab.Declaration", 21, 21);
x_15 = lean_mk_string_unchecked("_private.Lean.Elab.Declaration.0.Lean.Elab.Command.setDeclIdName", 64, 64);
x_16 = lean_unsigned_to_nat(29u);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_mk_string_unchecked("assertion violation: !(`_root_).isPrefixOf id\n  ", 48, 48);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_20 = l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(x_19);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_28; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getKind(x_9);
x_33 = lean_mk_string_unchecked("abbrev", 6, 6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_33);
x_35 = lean_name_eq(x_10, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_36);
x_38 = lean_name_eq(x_10, x_37);
lean_dec(x_37);
x_28 = x_38;
goto block_32;
}
else
{
x_28 = x_7;
goto block_32;
}
block_27:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = lean_name_eq(x_10, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_mk_string_unchecked("axiom", 5, 5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_15);
x_17 = lean_name_eq(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_mk_string_unchecked("inductive", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_18);
x_20 = lean_name_eq(x_10, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_mk_string_unchecked("classInductive", 14, 14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_21);
x_23 = lean_name_eq(x_10, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_mk_string_unchecked("structure", 9, 9);
x_25 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_24);
x_26 = lean_name_eq(x_10, x_25);
lean_dec(x_25);
lean_dec(x_10);
return x_26;
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
block_32:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_mk_string_unchecked("theorem", 7, 7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_29);
x_31 = lean_name_eq(x_10, x_30);
lean_dec(x_30);
x_11 = x_31;
goto block_27;
}
else
{
x_11 = x_7;
goto block_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = lean_mk_string_unchecked("instance", 8, 8);
x_12 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_11);
x_13 = lean_name_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Elab_expandDeclIdCore(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
x_15 = lean_box(0);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Syntax_getArg(x_17, x_16);
lean_dec(x_17);
x_19 = l_Lean_Elab_expandDeclIdCore(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_24; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_24 = l_Lean_Syntax_isNone(x_8);
if (x_24 == 0)
{
x_9 = x_4;
goto block_23;
}
else
{
x_9 = x_3;
goto block_23;
}
block_23:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("Lean.Elab.Declaration", 21, 21);
x_11 = lean_mk_string_unchecked("_private.Lean.Elab.Declaration.0.Lean.Elab.Command.setDefName", 61, 61);
x_12 = lean_unsigned_to_nat(80u);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_string_unchecked("assertion violation: !stx[1][3].isNone\n    ", 43, 43);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Lean_Parser_SyntaxStack_back_spec__0(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_8, x_17);
x_19 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(x_18, x_2);
x_20 = l_Lean_Syntax_setArg(x_8, x_17, x_19);
x_21 = l_Lean_Syntax_setArg(x_6, x_7, x_20);
x_22 = l_Lean_Syntax_setArg(x_1, x_5, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_27 = l_Lean_Syntax_getArg(x_26, x_25);
x_28 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(x_27, x_2);
x_29 = l_Lean_Syntax_setArg(x_26, x_25, x_28);
x_30 = l_Lean_Syntax_setArg(x_1, x_25, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_mk_string_unchecked("_root_", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Name_isPrefixOf(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = l_Lean_extractMacroScopes(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_box(0);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_15; 
lean_dec(x_12);
lean_free_object(x_4);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(x_14, x_2, x_3);
return x_15;
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_4);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Name_str___override(x_14, x_19);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 3);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Lean_MacroScopesView_review(x_24);
x_26 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_free_object(x_4);
lean_dec(x_1);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = l_Lean_Name_num___override(x_29, x_30);
x_32 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(x_31, x_2, x_3);
lean_dec(x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_4);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = l_Lean_Name_replacePrefix(x_8, x_10, x_33);
lean_dec(x_10);
x_35 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_34, x_2, x_3);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
lean_dec(x_4);
x_47 = lean_mk_string_unchecked("_root_", 6, 6);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = l_Lean_Name_isPrefixOf(x_48, x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_50 = l_Lean_extractMacroScopes(x_46);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_box(0);
switch (lean_obj_tag(x_51)) {
case 0:
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_1);
x_53 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(x_52, x_2, x_3);
return x_53;
}
case 1:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Lean_Name_str___override(x_52, x_57);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_50, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_50, 3);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_61);
x_63 = l_Lean_MacroScopesView_review(x_62);
x_64 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_3);
return x_67;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_1);
x_68 = lean_ctor_get(x_51, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_dec(x_51);
x_70 = l_Lean_Name_num___override(x_68, x_69);
x_71 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(x_70, x_2, x_3);
lean_dec(x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = l_Lean_Name_replacePrefix(x_46, x_48, x_72);
lean_dec(x_48);
x_74 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_73, x_2, x_3);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_4);
x_11 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_addTermInfo_x27(x_2, x_12, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_30 = lean_box(2);
x_31 = lean_unbox(x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
lean_inc(x_2);
x_32 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Elab_Term_elabType(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_41 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_box(1);
x_46 = lean_unbox(x_45);
x_47 = l_Lean_Syntax_getTailPos_x3f(x_4, x_46);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_48 = l_Lean_Elab_Term_addAutoBoundImplicits(x_10, x_47, x_11, x_12, x_13, x_14, x_15, x_16, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_37, x_14, x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_box(1);
x_56 = lean_unbox(x_39);
x_57 = lean_unbox(x_45);
x_58 = lean_unbox(x_55);
x_59 = l_Lean_Meta_mkForallFVars(x_49, x_53, x_56, x_57, x_58, x_13, x_14, x_15, x_16, x_54);
lean_dec(x_49);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_45);
x_63 = lean_unbox(x_45);
x_64 = lean_unbox(x_55);
x_65 = l_Lean_Meta_mkForallFVars(x_5, x_60, x_62, x_63, x_64, x_13, x_14, x_15, x_16, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_39);
x_69 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_66, x_68, x_12, x_14, x_67);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_unsigned_to_nat(8u);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_shiftl(x_73, x_6);
x_76 = lean_unsigned_to_nat(3u);
x_77 = lean_nat_div(x_75, x_76);
lean_dec(x_75);
x_78 = l_Nat_nextPowerOfTwo(x_77);
lean_dec(x_77);
x_79 = lean_box(0);
lean_inc(x_78);
x_80 = lean_mk_array(x_78, x_79);
lean_ctor_set(x_69, 1, x_80);
lean_ctor_set(x_69, 0, x_74);
x_81 = lean_box(0);
x_82 = lean_mk_array(x_78, x_81);
lean_ctor_set(x_51, 1, x_82);
lean_ctor_set(x_51, 0, x_74);
x_83 = lean_mk_empty_array_with_capacity(x_74);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_51);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_71);
x_85 = l_Lean_CollectLevelParams_main(x_71, x_84);
x_86 = lean_ctor_get(x_85, 2);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Elab_sortDeclLevelParams(x_7, x_8, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_71);
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_ctor_set_tag(x_87, 3);
x_89 = l_Lean_MessageData_ofFormat(x_87);
x_90 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_89, x_11, x_12, x_13, x_14, x_15, x_16, x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_93, x_11, x_12, x_13, x_14, x_15, x_16, x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_71, x_14, x_72);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_mk_string_unchecked("Elab", 4, 4);
x_102 = lean_mk_string_unchecked("axiom", 5, 5);
x_103 = l_Lean_Name_mkStr2(x_101, x_102);
lean_inc(x_103);
x_104 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_103, x_15, x_100);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_138; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_99);
lean_inc(x_2);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_2);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set(x_108, 2, x_99);
x_109 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_110 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_110, 0, x_2);
lean_closure_set(x_110, 1, x_4);
lean_closure_set(x_110, 2, x_45);
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_109);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_111);
x_138 = lean_unbox(x_106);
lean_dec(x_106);
if (x_138 == 0)
{
lean_free_object(x_104);
lean_dec(x_103);
lean_free_object(x_97);
lean_dec(x_99);
lean_free_object(x_41);
lean_free_object(x_32);
x_112 = x_11;
x_113 = x_12;
x_114 = x_13;
x_115 = x_14;
x_116 = x_15;
x_117 = x_16;
x_118 = x_107;
goto block_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_mk_string_unchecked("", 0, 0);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
lean_inc(x_2);
x_141 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_140);
lean_ctor_set_tag(x_104, 7);
lean_ctor_set(x_104, 1, x_141);
lean_ctor_set(x_104, 0, x_140);
x_142 = lean_mk_string_unchecked(" : ", 3, 3);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_143);
lean_ctor_set(x_97, 0, x_104);
x_144 = l_Lean_MessageData_ofExpr(x_99);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_144);
lean_ctor_set(x_41, 0, x_97);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_140);
lean_ctor_set(x_32, 0, x_41);
x_145 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_103, x_32, x_13, x_14, x_15, x_16, x_107);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_112 = x_11;
x_113 = x_12;
x_114 = x_13;
x_115 = x_14;
x_116 = x_15;
x_117 = x_16;
x_118 = x_146;
goto block_137;
}
block_137:
{
lean_object* x_119; 
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_87);
x_119 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_87, x_112, x_113, x_114, x_115, x_116, x_117, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_87);
x_121 = l_Lean_addDecl(x_87, x_116, x_117, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
x_123 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_110, x_112, x_113, x_114, x_115, x_116, x_117, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_box(0);
x_126 = lean_unbox(x_125);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_18);
lean_inc(x_2);
x_127 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_126, x_112, x_113, x_114, x_115, x_116, x_117, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_get(x_117, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_2);
x_133 = l_Lean_isExtern(x_132, x_2);
if (x_133 == 0)
{
lean_dec(x_87);
x_19 = x_112;
x_20 = x_113;
x_21 = x_114;
x_22 = x_115;
x_23 = x_116;
x_24 = x_117;
x_25 = x_131;
goto block_29;
}
else
{
uint8_t x_134; lean_object* x_135; 
x_134 = lean_unbox(x_45);
lean_inc(x_117);
lean_inc(x_116);
x_135 = l_Lean_compileDecl(x_87, x_134, x_116, x_117, x_131);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_19 = x_112;
x_20 = x_113;
x_21 = x_114;
x_22 = x_115;
x_23 = x_116;
x_24 = x_117;
x_25 = x_136;
goto block_29;
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_18);
lean_dec(x_2);
return x_135;
}
}
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_127;
}
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_123;
}
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_87);
lean_dec(x_110);
lean_dec(x_18);
lean_dec(x_2);
return x_121;
}
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_87);
lean_dec(x_110);
lean_dec(x_18);
lean_dec(x_2);
return x_119;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_179; 
x_147 = lean_ctor_get(x_104, 0);
x_148 = lean_ctor_get(x_104, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_104);
lean_inc(x_99);
lean_inc(x_2);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_2);
lean_ctor_set(x_149, 1, x_96);
lean_ctor_set(x_149, 2, x_99);
x_150 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_151 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_151, 0, x_2);
lean_closure_set(x_151, 1, x_4);
lean_closure_set(x_151, 2, x_45);
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_150);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_152);
x_179 = lean_unbox(x_147);
lean_dec(x_147);
if (x_179 == 0)
{
lean_dec(x_103);
lean_free_object(x_97);
lean_dec(x_99);
lean_free_object(x_41);
lean_free_object(x_32);
x_153 = x_11;
x_154 = x_12;
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = x_148;
goto block_178;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_180 = lean_mk_string_unchecked("", 0, 0);
x_181 = l_Lean_stringToMessageData(x_180);
lean_dec(x_180);
lean_inc(x_2);
x_182 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_181);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_mk_string_unchecked(" : ", 3, 3);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_185);
lean_ctor_set(x_97, 0, x_183);
x_186 = l_Lean_MessageData_ofExpr(x_99);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_186);
lean_ctor_set(x_41, 0, x_97);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_181);
lean_ctor_set(x_32, 0, x_41);
x_187 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_103, x_32, x_13, x_14, x_15, x_16, x_148);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_153 = x_11;
x_154 = x_12;
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = x_188;
goto block_178;
}
block_178:
{
lean_object* x_160; 
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_87);
x_160 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_87, x_153, x_154, x_155, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_87);
x_162 = l_Lean_addDecl(x_87, x_157, x_158, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
x_164 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_151, x_153, x_154, x_155, x_156, x_157, x_158, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_box(0);
x_167 = lean_unbox(x_166);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_18);
lean_inc(x_2);
x_168 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_167, x_153, x_154, x_155, x_156, x_157, x_158, x_165);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_st_ref_get(x_158, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_2);
x_174 = l_Lean_isExtern(x_173, x_2);
if (x_174 == 0)
{
lean_dec(x_87);
x_19 = x_153;
x_20 = x_154;
x_21 = x_155;
x_22 = x_156;
x_23 = x_157;
x_24 = x_158;
x_25 = x_172;
goto block_29;
}
else
{
uint8_t x_175; lean_object* x_176; 
x_175 = lean_unbox(x_45);
lean_inc(x_158);
lean_inc(x_157);
x_176 = l_Lean_compileDecl(x_87, x_175, x_157, x_158, x_172);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_19 = x_153;
x_20 = x_154;
x_21 = x_155;
x_22 = x_156;
x_23 = x_157;
x_24 = x_158;
x_25 = x_177;
goto block_29;
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_18);
lean_dec(x_2);
return x_176;
}
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_168;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_164;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_87);
lean_dec(x_151);
lean_dec(x_18);
lean_dec(x_2);
return x_162;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_87);
lean_dec(x_151);
lean_dec(x_18);
lean_dec(x_2);
return x_160;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_228; 
x_189 = lean_ctor_get(x_97, 0);
x_190 = lean_ctor_get(x_97, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_97);
x_191 = lean_mk_string_unchecked("Elab", 4, 4);
x_192 = lean_mk_string_unchecked("axiom", 5, 5);
x_193 = l_Lean_Name_mkStr2(x_191, x_192);
lean_inc(x_193);
x_194 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_193, x_15, x_190);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
lean_inc(x_189);
lean_inc(x_2);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_2);
lean_ctor_set(x_198, 1, x_96);
lean_ctor_set(x_198, 2, x_189);
x_199 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_200 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_200, 0, x_2);
lean_closure_set(x_200, 1, x_4);
lean_closure_set(x_200, 2, x_45);
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_199);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_201);
x_228 = lean_unbox(x_195);
lean_dec(x_195);
if (x_228 == 0)
{
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_189);
lean_free_object(x_41);
lean_free_object(x_32);
x_202 = x_11;
x_203 = x_12;
x_204 = x_13;
x_205 = x_14;
x_206 = x_15;
x_207 = x_16;
x_208 = x_196;
goto block_227;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_229 = lean_mk_string_unchecked("", 0, 0);
x_230 = l_Lean_stringToMessageData(x_229);
lean_dec(x_229);
lean_inc(x_2);
x_231 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_230);
if (lean_is_scalar(x_197)) {
 x_232 = lean_alloc_ctor(7, 2, 0);
} else {
 x_232 = x_197;
 lean_ctor_set_tag(x_232, 7);
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_mk_string_unchecked(" : ", 3, 3);
x_234 = l_Lean_stringToMessageData(x_233);
lean_dec(x_233);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_MessageData_ofExpr(x_189);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_236);
lean_ctor_set(x_41, 0, x_235);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_230);
lean_ctor_set(x_32, 0, x_41);
x_237 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_193, x_32, x_13, x_14, x_15, x_16, x_196);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_202 = x_11;
x_203 = x_12;
x_204 = x_13;
x_205 = x_14;
x_206 = x_15;
x_207 = x_16;
x_208 = x_238;
goto block_227;
}
block_227:
{
lean_object* x_209; 
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_87);
x_209 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_87, x_202, x_203, x_204, x_205, x_206, x_207, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_87);
x_211 = l_Lean_addDecl(x_87, x_206, x_207, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
x_213 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_200, x_202, x_203, x_204, x_205, x_206, x_207, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_box(0);
x_216 = lean_unbox(x_215);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_18);
lean_inc(x_2);
x_217 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_216, x_202, x_203, x_204, x_205, x_206, x_207, x_214);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_st_ref_get(x_207, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_2);
x_223 = l_Lean_isExtern(x_222, x_2);
if (x_223 == 0)
{
lean_dec(x_87);
x_19 = x_202;
x_20 = x_203;
x_21 = x_204;
x_22 = x_205;
x_23 = x_206;
x_24 = x_207;
x_25 = x_221;
goto block_29;
}
else
{
uint8_t x_224; lean_object* x_225; 
x_224 = lean_unbox(x_45);
lean_inc(x_207);
lean_inc(x_206);
x_225 = l_Lean_compileDecl(x_87, x_224, x_206, x_207, x_221);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_19 = x_202;
x_20 = x_203;
x_21 = x_204;
x_22 = x_205;
x_23 = x_206;
x_24 = x_207;
x_25 = x_226;
goto block_29;
}
else
{
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_18);
lean_dec(x_2);
return x_225;
}
}
}
else
{
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_217;
}
}
else
{
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_2);
return x_213;
}
}
else
{
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_87);
lean_dec(x_200);
lean_dec(x_18);
lean_dec(x_2);
return x_211;
}
}
else
{
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_87);
lean_dec(x_200);
lean_dec(x_18);
lean_dec(x_2);
return x_209;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_282; 
x_239 = lean_ctor_get(x_87, 0);
lean_inc(x_239);
lean_dec(x_87);
x_240 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_71, x_14, x_72);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_mk_string_unchecked("Elab", 4, 4);
x_245 = lean_mk_string_unchecked("axiom", 5, 5);
x_246 = l_Lean_Name_mkStr2(x_244, x_245);
lean_inc(x_246);
x_247 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_246, x_15, x_242);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
lean_inc(x_241);
lean_inc(x_2);
x_251 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_251, 0, x_2);
lean_ctor_set(x_251, 1, x_239);
lean_ctor_set(x_251, 2, x_241);
x_252 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_253 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_253, 0, x_2);
lean_closure_set(x_253, 1, x_4);
lean_closure_set(x_253, 2, x_45);
x_254 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_252);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_254);
x_282 = lean_unbox(x_248);
lean_dec(x_248);
if (x_282 == 0)
{
lean_dec(x_250);
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_241);
lean_free_object(x_41);
lean_free_object(x_32);
x_256 = x_11;
x_257 = x_12;
x_258 = x_13;
x_259 = x_14;
x_260 = x_15;
x_261 = x_16;
x_262 = x_249;
goto block_281;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_283 = lean_mk_string_unchecked("", 0, 0);
x_284 = l_Lean_stringToMessageData(x_283);
lean_dec(x_283);
lean_inc(x_2);
x_285 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_284);
if (lean_is_scalar(x_250)) {
 x_286 = lean_alloc_ctor(7, 2, 0);
} else {
 x_286 = x_250;
 lean_ctor_set_tag(x_286, 7);
}
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_mk_string_unchecked(" : ", 3, 3);
x_288 = l_Lean_stringToMessageData(x_287);
lean_dec(x_287);
if (lean_is_scalar(x_243)) {
 x_289 = lean_alloc_ctor(7, 2, 0);
} else {
 x_289 = x_243;
 lean_ctor_set_tag(x_289, 7);
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_MessageData_ofExpr(x_241);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_290);
lean_ctor_set(x_41, 0, x_289);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_284);
lean_ctor_set(x_32, 0, x_41);
x_291 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_246, x_32, x_13, x_14, x_15, x_16, x_249);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_256 = x_11;
x_257 = x_12;
x_258 = x_13;
x_259 = x_14;
x_260 = x_15;
x_261 = x_16;
x_262 = x_292;
goto block_281;
}
block_281:
{
lean_object* x_263; 
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
x_263 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_255, x_256, x_257, x_258, x_259, x_260, x_261, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_255);
x_265 = l_Lean_addDecl(x_255, x_260, x_261, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
x_267 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_253, x_256, x_257, x_258, x_259, x_260, x_261, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_box(0);
x_270 = lean_unbox(x_269);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_18);
lean_inc(x_2);
x_271 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_270, x_256, x_257, x_258, x_259, x_260, x_261, x_268);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_st_ref_get(x_261, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_2);
x_277 = l_Lean_isExtern(x_276, x_2);
if (x_277 == 0)
{
lean_dec(x_255);
x_19 = x_256;
x_20 = x_257;
x_21 = x_258;
x_22 = x_259;
x_23 = x_260;
x_24 = x_261;
x_25 = x_275;
goto block_29;
}
else
{
uint8_t x_278; lean_object* x_279; 
x_278 = lean_unbox(x_45);
lean_inc(x_261);
lean_inc(x_260);
x_279 = l_Lean_compileDecl(x_255, x_278, x_260, x_261, x_275);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_19 = x_256;
x_20 = x_257;
x_21 = x_258;
x_22 = x_259;
x_23 = x_260;
x_24 = x_261;
x_25 = x_280;
goto block_29;
}
else
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_18);
lean_dec(x_2);
return x_279;
}
}
}
else
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_18);
lean_dec(x_2);
return x_271;
}
}
else
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_18);
lean_dec(x_2);
return x_267;
}
}
else
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_18);
lean_dec(x_2);
return x_265;
}
}
else
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_18);
lean_dec(x_2);
return x_263;
}
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_293 = lean_ctor_get(x_69, 0);
x_294 = lean_ctor_get(x_69, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_69);
x_295 = lean_unsigned_to_nat(8u);
x_296 = lean_unsigned_to_nat(0u);
x_297 = lean_nat_shiftl(x_295, x_6);
x_298 = lean_unsigned_to_nat(3u);
x_299 = lean_nat_div(x_297, x_298);
lean_dec(x_297);
x_300 = l_Nat_nextPowerOfTwo(x_299);
lean_dec(x_299);
x_301 = lean_box(0);
lean_inc(x_300);
x_302 = lean_mk_array(x_300, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_296);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_box(0);
x_305 = lean_mk_array(x_300, x_304);
lean_ctor_set(x_51, 1, x_305);
lean_ctor_set(x_51, 0, x_296);
x_306 = lean_mk_empty_array_with_capacity(x_296);
x_307 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_51);
lean_ctor_set(x_307, 2, x_306);
lean_inc(x_293);
x_308 = l_Lean_CollectLevelParams_main(x_293, x_307);
x_309 = lean_ctor_get(x_308, 2);
lean_inc(x_309);
lean_dec(x_308);
x_310 = l_Lean_Elab_sortDeclLevelParams(x_7, x_8, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_293);
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(3, 1, 0);
} else {
 x_313 = x_312;
 lean_ctor_set_tag(x_313, 3);
}
lean_ctor_set(x_313, 0, x_311);
x_314 = l_Lean_MessageData_ofFormat(x_313);
x_315 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_314, x_11, x_12, x_13, x_14, x_15, x_16, x_294);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_360; 
x_316 = lean_ctor_get(x_310, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_317 = x_310;
} else {
 lean_dec_ref(x_310);
 x_317 = lean_box(0);
}
x_318 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_293, x_14, x_294);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
x_322 = lean_mk_string_unchecked("Elab", 4, 4);
x_323 = lean_mk_string_unchecked("axiom", 5, 5);
x_324 = l_Lean_Name_mkStr2(x_322, x_323);
lean_inc(x_324);
x_325 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_324, x_15, x_320);
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
lean_inc(x_319);
lean_inc(x_2);
x_329 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_329, 0, x_2);
lean_ctor_set(x_329, 1, x_316);
lean_ctor_set(x_329, 2, x_319);
x_330 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_331 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_331, 0, x_2);
lean_closure_set(x_331, 1, x_4);
lean_closure_set(x_331, 2, x_45);
x_332 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set_uint8(x_332, sizeof(void*)*1, x_330);
if (lean_is_scalar(x_317)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_317;
 lean_ctor_set_tag(x_333, 0);
}
lean_ctor_set(x_333, 0, x_332);
x_360 = lean_unbox(x_326);
lean_dec(x_326);
if (x_360 == 0)
{
lean_dec(x_328);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_319);
lean_free_object(x_41);
lean_free_object(x_32);
x_334 = x_11;
x_335 = x_12;
x_336 = x_13;
x_337 = x_14;
x_338 = x_15;
x_339 = x_16;
x_340 = x_327;
goto block_359;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_361 = lean_mk_string_unchecked("", 0, 0);
x_362 = l_Lean_stringToMessageData(x_361);
lean_dec(x_361);
lean_inc(x_2);
x_363 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_362);
if (lean_is_scalar(x_328)) {
 x_364 = lean_alloc_ctor(7, 2, 0);
} else {
 x_364 = x_328;
 lean_ctor_set_tag(x_364, 7);
}
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_mk_string_unchecked(" : ", 3, 3);
x_366 = l_Lean_stringToMessageData(x_365);
lean_dec(x_365);
if (lean_is_scalar(x_321)) {
 x_367 = lean_alloc_ctor(7, 2, 0);
} else {
 x_367 = x_321;
 lean_ctor_set_tag(x_367, 7);
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Lean_MessageData_ofExpr(x_319);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_368);
lean_ctor_set(x_41, 0, x_367);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_362);
lean_ctor_set(x_32, 0, x_41);
x_369 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_324, x_32, x_13, x_14, x_15, x_16, x_327);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_334 = x_11;
x_335 = x_12;
x_336 = x_13;
x_337 = x_14;
x_338 = x_15;
x_339 = x_16;
x_340 = x_370;
goto block_359;
}
block_359:
{
lean_object* x_341; 
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
x_341 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_333, x_334, x_335, x_336, x_337, x_338, x_339, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec(x_341);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_333);
x_343 = l_Lean_addDecl(x_333, x_338, x_339, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
x_345 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_331, x_334, x_335, x_336, x_337, x_338, x_339, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_box(0);
x_348 = lean_unbox(x_347);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_18);
lean_inc(x_2);
x_349 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_348, x_334, x_335, x_336, x_337, x_338, x_339, x_346);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_st_ref_get(x_339, x_350);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
lean_dec(x_352);
lean_inc(x_2);
x_355 = l_Lean_isExtern(x_354, x_2);
if (x_355 == 0)
{
lean_dec(x_333);
x_19 = x_334;
x_20 = x_335;
x_21 = x_336;
x_22 = x_337;
x_23 = x_338;
x_24 = x_339;
x_25 = x_353;
goto block_29;
}
else
{
uint8_t x_356; lean_object* x_357; 
x_356 = lean_unbox(x_45);
lean_inc(x_339);
lean_inc(x_338);
x_357 = l_Lean_compileDecl(x_333, x_356, x_338, x_339, x_353);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
lean_dec(x_357);
x_19 = x_334;
x_20 = x_335;
x_21 = x_336;
x_22 = x_337;
x_23 = x_338;
x_24 = x_339;
x_25 = x_358;
goto block_29;
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_18);
lean_dec(x_2);
return x_357;
}
}
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_18);
lean_dec(x_2);
return x_349;
}
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_18);
lean_dec(x_2);
return x_345;
}
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_18);
lean_dec(x_2);
return x_343;
}
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_18);
lean_dec(x_2);
return x_341;
}
}
}
}
}
else
{
uint8_t x_371; 
lean_free_object(x_51);
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_371 = !lean_is_exclusive(x_65);
if (x_371 == 0)
{
return x_65;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_65, 0);
x_373 = lean_ctor_get(x_65, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_65);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_free_object(x_51);
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_375 = !lean_is_exclusive(x_59);
if (x_375 == 0)
{
return x_59;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_59, 0);
x_377 = lean_ctor_get(x_59, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_59);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_383; uint8_t x_384; lean_object* x_385; 
x_379 = lean_ctor_get(x_51, 0);
x_380 = lean_ctor_get(x_51, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_51);
x_381 = lean_box(1);
x_382 = lean_unbox(x_39);
x_383 = lean_unbox(x_45);
x_384 = lean_unbox(x_381);
x_385 = l_Lean_Meta_mkForallFVars(x_49, x_379, x_382, x_383, x_384, x_13, x_14, x_15, x_16, x_380);
lean_dec(x_49);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; lean_object* x_391; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_unbox(x_45);
x_389 = lean_unbox(x_45);
x_390 = lean_unbox(x_381);
x_391 = l_Lean_Meta_mkForallFVars(x_5, x_386, x_388, x_389, x_390, x_13, x_14, x_15, x_16, x_387);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__0___boxed), 2, 1);
lean_closure_set(x_394, 0, x_39);
x_395 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_392, x_394, x_12, x_14, x_393);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_398 = x_395;
} else {
 lean_dec_ref(x_395);
 x_398 = lean_box(0);
}
x_399 = lean_unsigned_to_nat(8u);
x_400 = lean_unsigned_to_nat(0u);
x_401 = lean_nat_shiftl(x_399, x_6);
x_402 = lean_unsigned_to_nat(3u);
x_403 = lean_nat_div(x_401, x_402);
lean_dec(x_401);
x_404 = l_Nat_nextPowerOfTwo(x_403);
lean_dec(x_403);
x_405 = lean_box(0);
lean_inc(x_404);
x_406 = lean_mk_array(x_404, x_405);
if (lean_is_scalar(x_398)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_398;
}
lean_ctor_set(x_407, 0, x_400);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_box(0);
x_409 = lean_mk_array(x_404, x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_400);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_mk_empty_array_with_capacity(x_400);
x_412 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_412, 0, x_407);
lean_ctor_set(x_412, 1, x_410);
lean_ctor_set(x_412, 2, x_411);
lean_inc(x_396);
x_413 = l_Lean_CollectLevelParams_main(x_396, x_412);
x_414 = lean_ctor_get(x_413, 2);
lean_inc(x_414);
lean_dec(x_413);
x_415 = l_Lean_Elab_sortDeclLevelParams(x_7, x_8, x_414);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_396);
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(3, 1, 0);
} else {
 x_418 = x_417;
 lean_ctor_set_tag(x_418, 3);
}
lean_ctor_set(x_418, 0, x_416);
x_419 = l_Lean_MessageData_ofFormat(x_418);
x_420 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_419, x_11, x_12, x_13, x_14, x_15, x_16, x_397);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_465; 
x_421 = lean_ctor_get(x_415, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_422 = x_415;
} else {
 lean_dec_ref(x_415);
 x_422 = lean_box(0);
}
x_423 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_396, x_14, x_397);
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
x_427 = lean_mk_string_unchecked("Elab", 4, 4);
x_428 = lean_mk_string_unchecked("axiom", 5, 5);
x_429 = l_Lean_Name_mkStr2(x_427, x_428);
lean_inc(x_429);
x_430 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_429, x_15, x_425);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
lean_inc(x_424);
lean_inc(x_2);
x_434 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_434, 0, x_2);
lean_ctor_set(x_434, 1, x_421);
lean_ctor_set(x_434, 2, x_424);
x_435 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_436 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_436, 0, x_2);
lean_closure_set(x_436, 1, x_4);
lean_closure_set(x_436, 2, x_45);
x_437 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set_uint8(x_437, sizeof(void*)*1, x_435);
if (lean_is_scalar(x_422)) {
 x_438 = lean_alloc_ctor(0, 1, 0);
} else {
 x_438 = x_422;
 lean_ctor_set_tag(x_438, 0);
}
lean_ctor_set(x_438, 0, x_437);
x_465 = lean_unbox(x_431);
lean_dec(x_431);
if (x_465 == 0)
{
lean_dec(x_433);
lean_dec(x_429);
lean_dec(x_426);
lean_dec(x_424);
lean_free_object(x_41);
lean_free_object(x_32);
x_439 = x_11;
x_440 = x_12;
x_441 = x_13;
x_442 = x_14;
x_443 = x_15;
x_444 = x_16;
x_445 = x_432;
goto block_464;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_466 = lean_mk_string_unchecked("", 0, 0);
x_467 = l_Lean_stringToMessageData(x_466);
lean_dec(x_466);
lean_inc(x_2);
x_468 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_467);
if (lean_is_scalar(x_433)) {
 x_469 = lean_alloc_ctor(7, 2, 0);
} else {
 x_469 = x_433;
 lean_ctor_set_tag(x_469, 7);
}
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_mk_string_unchecked(" : ", 3, 3);
x_471 = l_Lean_stringToMessageData(x_470);
lean_dec(x_470);
if (lean_is_scalar(x_426)) {
 x_472 = lean_alloc_ctor(7, 2, 0);
} else {
 x_472 = x_426;
 lean_ctor_set_tag(x_472, 7);
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_MessageData_ofExpr(x_424);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_473);
lean_ctor_set(x_41, 0, x_472);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_467);
lean_ctor_set(x_32, 0, x_41);
x_474 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_429, x_32, x_13, x_14, x_15, x_16, x_432);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_439 = x_11;
x_440 = x_12;
x_441 = x_13;
x_442 = x_14;
x_443 = x_15;
x_444 = x_16;
x_445 = x_475;
goto block_464;
}
block_464:
{
lean_object* x_446; 
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
x_446 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_438, x_439, x_440, x_441, x_442, x_443, x_444, x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_438);
x_448 = l_Lean_addDecl(x_438, x_443, x_444, x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
x_450 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_436, x_439, x_440, x_441, x_442, x_443, x_444, x_449);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; 
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_452 = lean_box(0);
x_453 = lean_unbox(x_452);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_18);
lean_inc(x_2);
x_454 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_453, x_439, x_440, x_441, x_442, x_443, x_444, x_451);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_st_ref_get(x_444, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
lean_dec(x_457);
lean_inc(x_2);
x_460 = l_Lean_isExtern(x_459, x_2);
if (x_460 == 0)
{
lean_dec(x_438);
x_19 = x_439;
x_20 = x_440;
x_21 = x_441;
x_22 = x_442;
x_23 = x_443;
x_24 = x_444;
x_25 = x_458;
goto block_29;
}
else
{
uint8_t x_461; lean_object* x_462; 
x_461 = lean_unbox(x_45);
lean_inc(x_444);
lean_inc(x_443);
x_462 = l_Lean_compileDecl(x_438, x_461, x_443, x_444, x_458);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
lean_dec(x_462);
x_19 = x_439;
x_20 = x_440;
x_21 = x_441;
x_22 = x_442;
x_23 = x_443;
x_24 = x_444;
x_25 = x_463;
goto block_29;
}
else
{
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_18);
lean_dec(x_2);
return x_462;
}
}
}
else
{
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_18);
lean_dec(x_2);
return x_454;
}
}
else
{
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_18);
lean_dec(x_2);
return x_450;
}
}
else
{
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_436);
lean_dec(x_18);
lean_dec(x_2);
return x_448;
}
}
else
{
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_436);
lean_dec(x_18);
lean_dec(x_2);
return x_446;
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_476 = lean_ctor_get(x_391, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_391, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_478 = x_391;
} else {
 lean_dec_ref(x_391);
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
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_free_object(x_41);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_480 = lean_ctor_get(x_385, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_385, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_482 = x_385;
} else {
 lean_dec_ref(x_385);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
}
else
{
uint8_t x_484; 
lean_free_object(x_41);
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_484 = !lean_is_exclusive(x_48);
if (x_484 == 0)
{
return x_48;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_48, 0);
x_486 = lean_ctor_get(x_48, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_48);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; lean_object* x_492; 
x_488 = lean_ctor_get(x_41, 1);
lean_inc(x_488);
lean_dec(x_41);
x_489 = lean_box(1);
x_490 = lean_unbox(x_489);
x_491 = l_Lean_Syntax_getTailPos_x3f(x_4, x_490);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_492 = l_Lean_Elab_Term_addAutoBoundImplicits(x_10, x_491, x_11, x_12, x_13, x_14, x_15, x_16, x_488);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; lean_object* x_503; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_495 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_37, x_14, x_494);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
x_499 = lean_box(1);
x_500 = lean_unbox(x_39);
x_501 = lean_unbox(x_489);
x_502 = lean_unbox(x_499);
x_503 = l_Lean_Meta_mkForallFVars(x_493, x_496, x_500, x_501, x_502, x_13, x_14, x_15, x_16, x_497);
lean_dec(x_493);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_507; uint8_t x_508; lean_object* x_509; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_unbox(x_489);
x_507 = lean_unbox(x_489);
x_508 = lean_unbox(x_499);
x_509 = l_Lean_Meta_mkForallFVars(x_5, x_504, x_506, x_507, x_508, x_13, x_14, x_15, x_16, x_505);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__0___boxed), 2, 1);
lean_closure_set(x_512, 0, x_39);
x_513 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_510, x_512, x_12, x_14, x_511);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = lean_unsigned_to_nat(8u);
x_518 = lean_unsigned_to_nat(0u);
x_519 = lean_nat_shiftl(x_517, x_6);
x_520 = lean_unsigned_to_nat(3u);
x_521 = lean_nat_div(x_519, x_520);
lean_dec(x_519);
x_522 = l_Nat_nextPowerOfTwo(x_521);
lean_dec(x_521);
x_523 = lean_box(0);
lean_inc(x_522);
x_524 = lean_mk_array(x_522, x_523);
if (lean_is_scalar(x_516)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_516;
}
lean_ctor_set(x_525, 0, x_518);
lean_ctor_set(x_525, 1, x_524);
x_526 = lean_box(0);
x_527 = lean_mk_array(x_522, x_526);
if (lean_is_scalar(x_498)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_498;
}
lean_ctor_set(x_528, 0, x_518);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_mk_empty_array_with_capacity(x_518);
x_530 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_530, 0, x_525);
lean_ctor_set(x_530, 1, x_528);
lean_ctor_set(x_530, 2, x_529);
lean_inc(x_514);
x_531 = l_Lean_CollectLevelParams_main(x_514, x_530);
x_532 = lean_ctor_get(x_531, 2);
lean_inc(x_532);
lean_dec(x_531);
x_533 = l_Lean_Elab_sortDeclLevelParams(x_7, x_8, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_514);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_535 = x_533;
} else {
 lean_dec_ref(x_533);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(3, 1, 0);
} else {
 x_536 = x_535;
 lean_ctor_set_tag(x_536, 3);
}
lean_ctor_set(x_536, 0, x_534);
x_537 = l_Lean_MessageData_ofFormat(x_536);
x_538 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_537, x_11, x_12, x_13, x_14, x_15, x_16, x_515);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_538;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_583; 
x_539 = lean_ctor_get(x_533, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_540 = x_533;
} else {
 lean_dec_ref(x_533);
 x_540 = lean_box(0);
}
x_541 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_514, x_14, x_515);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_544 = x_541;
} else {
 lean_dec_ref(x_541);
 x_544 = lean_box(0);
}
x_545 = lean_mk_string_unchecked("Elab", 4, 4);
x_546 = lean_mk_string_unchecked("axiom", 5, 5);
x_547 = l_Lean_Name_mkStr2(x_545, x_546);
lean_inc(x_547);
x_548 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_547, x_15, x_543);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_551 = x_548;
} else {
 lean_dec_ref(x_548);
 x_551 = lean_box(0);
}
lean_inc(x_542);
lean_inc(x_2);
x_552 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_552, 0, x_2);
lean_ctor_set(x_552, 1, x_539);
lean_ctor_set(x_552, 2, x_542);
x_553 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_554 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_554, 0, x_2);
lean_closure_set(x_554, 1, x_4);
lean_closure_set(x_554, 2, x_489);
x_555 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set_uint8(x_555, sizeof(void*)*1, x_553);
if (lean_is_scalar(x_540)) {
 x_556 = lean_alloc_ctor(0, 1, 0);
} else {
 x_556 = x_540;
 lean_ctor_set_tag(x_556, 0);
}
lean_ctor_set(x_556, 0, x_555);
x_583 = lean_unbox(x_549);
lean_dec(x_549);
if (x_583 == 0)
{
lean_dec(x_551);
lean_dec(x_547);
lean_dec(x_544);
lean_dec(x_542);
lean_free_object(x_32);
x_557 = x_11;
x_558 = x_12;
x_559 = x_13;
x_560 = x_14;
x_561 = x_15;
x_562 = x_16;
x_563 = x_550;
goto block_582;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_584 = lean_mk_string_unchecked("", 0, 0);
x_585 = l_Lean_stringToMessageData(x_584);
lean_dec(x_584);
lean_inc(x_2);
x_586 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_585);
if (lean_is_scalar(x_551)) {
 x_587 = lean_alloc_ctor(7, 2, 0);
} else {
 x_587 = x_551;
 lean_ctor_set_tag(x_587, 7);
}
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_mk_string_unchecked(" : ", 3, 3);
x_589 = l_Lean_stringToMessageData(x_588);
lean_dec(x_588);
if (lean_is_scalar(x_544)) {
 x_590 = lean_alloc_ctor(7, 2, 0);
} else {
 x_590 = x_544;
 lean_ctor_set_tag(x_590, 7);
}
lean_ctor_set(x_590, 0, x_587);
lean_ctor_set(x_590, 1, x_589);
x_591 = l_Lean_MessageData_ofExpr(x_542);
x_592 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_585);
lean_ctor_set(x_32, 0, x_592);
x_593 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_547, x_32, x_13, x_14, x_15, x_16, x_550);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
lean_dec(x_593);
x_557 = x_11;
x_558 = x_12;
x_559 = x_13;
x_560 = x_14;
x_561 = x_15;
x_562 = x_16;
x_563 = x_594;
goto block_582;
}
block_582:
{
lean_object* x_564; 
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_560);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
x_564 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_556, x_557, x_558, x_559, x_560, x_561, x_562, x_563);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_556);
x_566 = l_Lean_addDecl(x_556, x_561, x_562, x_565);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_560);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
x_568 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_554, x_557, x_558, x_559, x_560, x_561, x_562, x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; 
x_569 = lean_ctor_get(x_568, 1);
lean_inc(x_569);
lean_dec(x_568);
x_570 = lean_box(0);
x_571 = lean_unbox(x_570);
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_560);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_18);
lean_inc(x_2);
x_572 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_571, x_557, x_558, x_559, x_560, x_561, x_562, x_569);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
lean_dec(x_572);
x_574 = lean_st_ref_get(x_562, x_573);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc(x_577);
lean_dec(x_575);
lean_inc(x_2);
x_578 = l_Lean_isExtern(x_577, x_2);
if (x_578 == 0)
{
lean_dec(x_556);
x_19 = x_557;
x_20 = x_558;
x_21 = x_559;
x_22 = x_560;
x_23 = x_561;
x_24 = x_562;
x_25 = x_576;
goto block_29;
}
else
{
uint8_t x_579; lean_object* x_580; 
x_579 = lean_unbox(x_489);
lean_inc(x_562);
lean_inc(x_561);
x_580 = l_Lean_compileDecl(x_556, x_579, x_561, x_562, x_576);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; 
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
lean_dec(x_580);
x_19 = x_557;
x_20 = x_558;
x_21 = x_559;
x_22 = x_560;
x_23 = x_561;
x_24 = x_562;
x_25 = x_581;
goto block_29;
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_18);
lean_dec(x_2);
return x_580;
}
}
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_2);
return x_572;
}
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_2);
return x_568;
}
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_554);
lean_dec(x_18);
lean_dec(x_2);
return x_566;
}
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_554);
lean_dec(x_18);
lean_dec(x_2);
return x_564;
}
}
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_498);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_595 = lean_ctor_get(x_509, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_509, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_597 = x_509;
} else {
 lean_dec_ref(x_509);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_596);
return x_598;
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_498);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_599 = lean_ctor_get(x_503, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_503, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_601 = x_503;
} else {
 lean_dec_ref(x_503);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_600);
return x_602;
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_603 = lean_ctor_get(x_492, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_492, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_605 = x_492;
} else {
 lean_dec_ref(x_492);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_603);
lean_ctor_set(x_606, 1, x_604);
return x_606;
}
}
}
else
{
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_41;
}
}
else
{
uint8_t x_607; 
lean_free_object(x_32);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_607 = !lean_is_exclusive(x_36);
if (x_607 == 0)
{
return x_36;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_608 = lean_ctor_get(x_36, 0);
x_609 = lean_ctor_get(x_36, 1);
lean_inc(x_609);
lean_inc(x_608);
lean_dec(x_36);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set(x_610, 1, x_609);
return x_610;
}
}
}
else
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_32, 1);
lean_inc(x_611);
lean_dec(x_32);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_612 = l_Lean_Elab_Term_elabType(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_box(0);
x_616 = lean_unbox(x_615);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_617 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_616, x_11, x_12, x_13, x_14, x_15, x_16, x_614);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_619 = x_617;
} else {
 lean_dec_ref(x_617);
 x_619 = lean_box(0);
}
x_620 = lean_box(1);
x_621 = lean_unbox(x_620);
x_622 = l_Lean_Syntax_getTailPos_x3f(x_4, x_621);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_623 = l_Lean_Elab_Term_addAutoBoundImplicits(x_10, x_622, x_11, x_12, x_13, x_14, x_15, x_16, x_618);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_632; uint8_t x_633; lean_object* x_634; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_613, x_14, x_625);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_629 = x_626;
} else {
 lean_dec_ref(x_626);
 x_629 = lean_box(0);
}
x_630 = lean_box(1);
x_631 = lean_unbox(x_615);
x_632 = lean_unbox(x_620);
x_633 = lean_unbox(x_630);
x_634 = l_Lean_Meta_mkForallFVars(x_624, x_627, x_631, x_632, x_633, x_13, x_14, x_15, x_16, x_628);
lean_dec(x_624);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; uint8_t x_637; uint8_t x_638; uint8_t x_639; lean_object* x_640; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_637 = lean_unbox(x_620);
x_638 = lean_unbox(x_620);
x_639 = lean_unbox(x_630);
x_640 = l_Lean_Meta_mkForallFVars(x_5, x_635, x_637, x_638, x_639, x_13, x_14, x_15, x_16, x_636);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__0___boxed), 2, 1);
lean_closure_set(x_643, 0, x_615);
x_644 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_641, x_643, x_12, x_14, x_642);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_647 = x_644;
} else {
 lean_dec_ref(x_644);
 x_647 = lean_box(0);
}
x_648 = lean_unsigned_to_nat(8u);
x_649 = lean_unsigned_to_nat(0u);
x_650 = lean_nat_shiftl(x_648, x_6);
x_651 = lean_unsigned_to_nat(3u);
x_652 = lean_nat_div(x_650, x_651);
lean_dec(x_650);
x_653 = l_Nat_nextPowerOfTwo(x_652);
lean_dec(x_652);
x_654 = lean_box(0);
lean_inc(x_653);
x_655 = lean_mk_array(x_653, x_654);
if (lean_is_scalar(x_647)) {
 x_656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_656 = x_647;
}
lean_ctor_set(x_656, 0, x_649);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_box(0);
x_658 = lean_mk_array(x_653, x_657);
if (lean_is_scalar(x_629)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_629;
}
lean_ctor_set(x_659, 0, x_649);
lean_ctor_set(x_659, 1, x_658);
x_660 = lean_mk_empty_array_with_capacity(x_649);
x_661 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_661, 0, x_656);
lean_ctor_set(x_661, 1, x_659);
lean_ctor_set(x_661, 2, x_660);
lean_inc(x_645);
x_662 = l_Lean_CollectLevelParams_main(x_645, x_661);
x_663 = lean_ctor_get(x_662, 2);
lean_inc(x_663);
lean_dec(x_662);
x_664 = l_Lean_Elab_sortDeclLevelParams(x_7, x_8, x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_645);
lean_dec(x_619);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_666 = x_664;
} else {
 lean_dec_ref(x_664);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(3, 1, 0);
} else {
 x_667 = x_666;
 lean_ctor_set_tag(x_667, 3);
}
lean_ctor_set(x_667, 0, x_665);
x_668 = l_Lean_MessageData_ofFormat(x_667);
x_669 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_668, x_11, x_12, x_13, x_14, x_15, x_16, x_646);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_714; 
x_670 = lean_ctor_get(x_664, 0);
lean_inc(x_670);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_671 = x_664;
} else {
 lean_dec_ref(x_664);
 x_671 = lean_box(0);
}
x_672 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_645, x_14, x_646);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 lean_ctor_release(x_672, 1);
 x_675 = x_672;
} else {
 lean_dec_ref(x_672);
 x_675 = lean_box(0);
}
x_676 = lean_mk_string_unchecked("Elab", 4, 4);
x_677 = lean_mk_string_unchecked("axiom", 5, 5);
x_678 = l_Lean_Name_mkStr2(x_676, x_677);
lean_inc(x_678);
x_679 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_678, x_15, x_674);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
lean_inc(x_673);
lean_inc(x_2);
x_683 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_683, 0, x_2);
lean_ctor_set(x_683, 1, x_670);
lean_ctor_set(x_683, 2, x_673);
x_684 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
lean_dec(x_1);
lean_inc(x_2);
x_685 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__1___boxed), 10, 3);
lean_closure_set(x_685, 0, x_2);
lean_closure_set(x_685, 1, x_4);
lean_closure_set(x_685, 2, x_620);
x_686 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set_uint8(x_686, sizeof(void*)*1, x_684);
if (lean_is_scalar(x_671)) {
 x_687 = lean_alloc_ctor(0, 1, 0);
} else {
 x_687 = x_671;
 lean_ctor_set_tag(x_687, 0);
}
lean_ctor_set(x_687, 0, x_686);
x_714 = lean_unbox(x_680);
lean_dec(x_680);
if (x_714 == 0)
{
lean_dec(x_682);
lean_dec(x_678);
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_619);
x_688 = x_11;
x_689 = x_12;
x_690 = x_13;
x_691 = x_14;
x_692 = x_15;
x_693 = x_16;
x_694 = x_681;
goto block_713;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_715 = lean_mk_string_unchecked("", 0, 0);
x_716 = l_Lean_stringToMessageData(x_715);
lean_dec(x_715);
lean_inc(x_2);
x_717 = l_Lean_MessageData_ofName(x_2);
lean_inc(x_716);
if (lean_is_scalar(x_682)) {
 x_718 = lean_alloc_ctor(7, 2, 0);
} else {
 x_718 = x_682;
 lean_ctor_set_tag(x_718, 7);
}
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
x_719 = lean_mk_string_unchecked(" : ", 3, 3);
x_720 = l_Lean_stringToMessageData(x_719);
lean_dec(x_719);
if (lean_is_scalar(x_675)) {
 x_721 = lean_alloc_ctor(7, 2, 0);
} else {
 x_721 = x_675;
 lean_ctor_set_tag(x_721, 7);
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_720);
x_722 = l_Lean_MessageData_ofExpr(x_673);
if (lean_is_scalar(x_619)) {
 x_723 = lean_alloc_ctor(7, 2, 0);
} else {
 x_723 = x_619;
 lean_ctor_set_tag(x_723, 7);
}
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
x_724 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_716);
x_725 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_678, x_724, x_13, x_14, x_15, x_16, x_681);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_688 = x_11;
x_689 = x_12;
x_690 = x_13;
x_691 = x_14;
x_692 = x_15;
x_693 = x_16;
x_694 = x_726;
goto block_713;
}
block_713:
{
lean_object* x_695; 
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
x_695 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_687, x_688, x_689, x_690, x_691, x_692, x_693, x_694);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; 
x_696 = lean_ctor_get(x_695, 1);
lean_inc(x_696);
lean_dec(x_695);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_687);
x_697 = l_Lean_addDecl(x_687, x_692, x_693, x_696);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec(x_697);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
x_699 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0(lean_box(0), x_685, x_688, x_689, x_690, x_691, x_692, x_693, x_698);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; 
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
x_701 = lean_box(0);
x_702 = lean_unbox(x_701);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_18);
lean_inc(x_2);
x_703 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_702, x_688, x_689, x_690, x_691, x_692, x_693, x_700);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; 
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
lean_dec(x_703);
x_705 = lean_st_ref_get(x_693, x_704);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
lean_dec(x_705);
x_708 = lean_ctor_get(x_706, 0);
lean_inc(x_708);
lean_dec(x_706);
lean_inc(x_2);
x_709 = l_Lean_isExtern(x_708, x_2);
if (x_709 == 0)
{
lean_dec(x_687);
x_19 = x_688;
x_20 = x_689;
x_21 = x_690;
x_22 = x_691;
x_23 = x_692;
x_24 = x_693;
x_25 = x_707;
goto block_29;
}
else
{
uint8_t x_710; lean_object* x_711; 
x_710 = lean_unbox(x_620);
lean_inc(x_693);
lean_inc(x_692);
x_711 = l_Lean_compileDecl(x_687, x_710, x_692, x_693, x_707);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; 
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec(x_711);
x_19 = x_688;
x_20 = x_689;
x_21 = x_690;
x_22 = x_691;
x_23 = x_692;
x_24 = x_693;
x_25 = x_712;
goto block_29;
}
else
{
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_18);
lean_dec(x_2);
return x_711;
}
}
}
else
{
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_687);
lean_dec(x_18);
lean_dec(x_2);
return x_703;
}
}
else
{
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_687);
lean_dec(x_18);
lean_dec(x_2);
return x_699;
}
}
else
{
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_687);
lean_dec(x_685);
lean_dec(x_18);
lean_dec(x_2);
return x_697;
}
}
else
{
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_687);
lean_dec(x_685);
lean_dec(x_18);
lean_dec(x_2);
return x_695;
}
}
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_629);
lean_dec(x_619);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_727 = lean_ctor_get(x_640, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_640, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_729 = x_640;
} else {
 lean_dec_ref(x_640);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_629);
lean_dec(x_619);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_731 = lean_ctor_get(x_634, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_634, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_733 = x_634;
} else {
 lean_dec_ref(x_634);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_731);
lean_ctor_set(x_734, 1, x_732);
return x_734;
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_619);
lean_dec(x_613);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_735 = lean_ctor_get(x_623, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_623, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_737 = x_623;
} else {
 lean_dec_ref(x_623);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
else
{
lean_dec(x_613);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_617;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_739 = lean_ctor_get(x_612, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_612, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_741 = x_612;
} else {
 lean_dec_ref(x_612);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
block_29:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_18, x_27, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_28;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabAxiom___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Elab_Term_getLevelNames(x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 6);
lean_inc(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_19 = l_Lean_Elab_Term_expandDeclId(x_18, x_16, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_23);
x_26 = l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Term_elabMutualDef_go_spec__0(x_23, x_25, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_24);
lean_inc(x_23);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__2___boxed), 17, 9);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_23);
lean_closure_set(x_28, 2, x_4);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_7);
lean_closure_set(x_28, 5, x_5);
lean_closure_set(x_28, 6, x_16);
lean_closure_set(x_28, 7, x_24);
lean_closure_set(x_28, 8, x_3);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__3___boxed), 2, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = l_Lean_Syntax_getArgs(x_6);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders), 10, 3);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_28);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLevelNames), 10, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, x_24);
lean_closure_set(x_32, 2, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_23);
lean_closure_set(x_33, 2, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitForbiddenPred), 10, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, x_29);
lean_closure_set(x_34, 2, x_33);
x_35 = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
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
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lam__4___boxed), 14, 6);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_9);
x_14 = l_Lean_Elab_Command_runTermElabM___redArg(x_13, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Command_elabAxiom___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Command_elabAxiom___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Command_elabAxiom___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Command_elabAxiom___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabAxiom___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabAxiom(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_2, 5);
x_20 = l_Lean_replaceRef(x_17, x_19);
x_21 = lean_unbox(x_18);
x_22 = l_Lean_SourceInfo_fromRef(x_20, x_21);
lean_dec(x_20);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Parser", 6, 6);
x_27 = lean_mk_string_unchecked("Command", 7, 7);
x_28 = lean_mk_string_unchecked("namespace", 9, 9);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
lean_inc(x_22);
lean_ctor_set_tag(x_8, 2);
lean_ctor_set(x_8, 1, x_28);
lean_ctor_set(x_8, 0, x_22);
x_30 = lean_unbox(x_18);
x_31 = l_Lean_mkIdentFrom(x_17, x_12, x_30);
lean_dec(x_17);
lean_inc(x_31);
lean_inc(x_22);
x_32 = l_Lean_Syntax_node2(x_22, x_29, x_8, x_31);
x_33 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_33);
x_34 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_33);
lean_inc(x_22);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_33);
lean_inc(x_24);
lean_inc(x_22);
x_36 = l_Lean_Syntax_node1(x_22, x_24, x_31);
lean_inc(x_22);
x_37 = l_Lean_Syntax_node2(x_22, x_34, x_35, x_36);
x_38 = l_Lean_Syntax_node3(x_22, x_24, x_32, x_13, x_37);
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Syntax_getArg(x_42, x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = lean_ctor_get(x_2, 5);
x_47 = l_Lean_replaceRef(x_44, x_46);
x_48 = lean_unbox(x_45);
x_49 = l_Lean_SourceInfo_fromRef(x_47, x_48);
lean_dec(x_47);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = lean_mk_string_unchecked("Lean", 4, 4);
x_53 = lean_mk_string_unchecked("Parser", 6, 6);
x_54 = lean_mk_string_unchecked("Command", 7, 7);
x_55 = lean_mk_string_unchecked("namespace", 9, 9);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_55);
lean_inc(x_49);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_unbox(x_45);
x_59 = l_Lean_mkIdentFrom(x_44, x_39, x_58);
lean_dec(x_44);
lean_inc(x_59);
lean_inc(x_49);
x_60 = l_Lean_Syntax_node2(x_49, x_56, x_57, x_59);
x_61 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_61);
x_62 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_61);
lean_inc(x_49);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_61);
lean_inc(x_51);
lean_inc(x_49);
x_64 = l_Lean_Syntax_node1(x_49, x_51, x_59);
lean_inc(x_49);
x_65 = l_Lean_Syntax_node2(x_49, x_62, x_63, x_64);
x_66 = l_Lean_Syntax_node3(x_49, x_51, x_60, x_40, x_65);
lean_ctor_set(x_4, 0, x_66);
return x_4;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_67 = lean_ctor_get(x_4, 1);
lean_inc(x_67);
lean_dec(x_4);
x_68 = lean_ctor_get(x_8, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_70 = x_8;
} else {
 lean_dec_ref(x_8);
 x_70 = lean_box(0);
}
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_Syntax_getArg(x_1, x_71);
lean_dec(x_1);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Syntax_getArg(x_72, x_73);
lean_dec(x_72);
x_75 = lean_box(0);
x_76 = lean_ctor_get(x_2, 5);
x_77 = l_Lean_replaceRef(x_74, x_76);
x_78 = lean_unbox(x_75);
x_79 = l_Lean_SourceInfo_fromRef(x_77, x_78);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("null", 4, 4);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = lean_mk_string_unchecked("Lean", 4, 4);
x_83 = lean_mk_string_unchecked("Parser", 6, 6);
x_84 = lean_mk_string_unchecked("Command", 7, 7);
x_85 = lean_mk_string_unchecked("namespace", 9, 9);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_86 = l_Lean_Name_mkStr4(x_82, x_83, x_84, x_85);
lean_inc(x_79);
if (lean_is_scalar(x_70)) {
 x_87 = lean_alloc_ctor(2, 2, 0);
} else {
 x_87 = x_70;
 lean_ctor_set_tag(x_87, 2);
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_unbox(x_75);
x_89 = l_Lean_mkIdentFrom(x_74, x_68, x_88);
lean_dec(x_74);
lean_inc(x_89);
lean_inc(x_79);
x_90 = l_Lean_Syntax_node2(x_79, x_86, x_87, x_89);
x_91 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_91);
x_92 = l_Lean_Name_mkStr4(x_82, x_83, x_84, x_91);
lean_inc(x_79);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_79);
lean_ctor_set(x_93, 1, x_91);
lean_inc(x_81);
lean_inc(x_79);
x_94 = l_Lean_Syntax_node1(x_79, x_81, x_89);
lean_inc(x_79);
x_95 = l_Lean_Syntax_node2(x_79, x_92, x_93, x_94);
x_96 = l_Lean_Syntax_node3(x_79, x_81, x_90, x_69, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_67);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
return x_4;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_4, 0);
x_100 = lean_ctor_get(x_4, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_4);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNamespacedDeclaration(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandNamespacedDeclaration", 27, 27);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandNamespacedDeclaration___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandNamespacedDeclaration", 27, 27);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Macro that expands a declaration with a complex name into an explicit `namespace` block.\nImplementing this step as a macro means that reuse checking is handled by `elabCommand`.\n ", 179, 179);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandNamespacedDeclaration", 27, 27);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(196u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(203u);
x_11 = lean_unsigned_to_nat(34u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(31u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Environment_setExporting(x_8, x_2);
lean_dec(x_8);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 8);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set(x_18, 4, x_13);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_15);
lean_ctor_set(x_18, 7, x_16);
lean_ctor_set(x_18, 8, x_17);
x_19 = lean_st_ref_set(x_1, x_18, x_7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_mk_string_unchecked("inductive", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_20);
x_22 = lean_name_eq(x_7, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_mk_string_unchecked("classInductive", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_name_eq(x_7, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_string_unchecked("structure", 9, 9);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_name_eq(x_7, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_mk_string_unchecked("unexpected declaration", 22, 22);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_30, x_8, x_9, x_10);
lean_dec(x_9);
return x_31;
}
else
{
goto block_19;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_19;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_19;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_8);
x_32 = l_Lean_Elab_elabModifiers___at___Lean_Elab_Command_elabMutualInductive_spec__0(x_2, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Command_elabAxiom(x_33, x_3, x_8, x_9, x_34);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
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
block_19:
{
lean_object* x_11; 
lean_inc(x_8);
x_11 = l_Lean_Elab_elabModifiers___at___Lean_Elab_Command_elabMutualInductive_spec__0(x_2, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Command_elabInductive(x_12, x_3, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_24 = lean_st_ref_get(x_3, x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_elabDeclaration___lam__0(x_25, x_2, x_3, x_26);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Command_elabDeclaration___lam__0(x_31, x_2, x_3, x_32);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_take(x_3, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Environment_header(x_34);
lean_dec(x_34);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 4);
lean_dec(x_39);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = l_Lean_Environment_setExporting(x_41, x_40);
lean_dec(x_41);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_37, 6);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 7);
lean_inc(x_49);
x_50 = lean_ctor_get(x_37, 8);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
lean_ctor_set(x_51, 7, x_49);
lean_ctor_set(x_51, 8, x_50);
x_52 = lean_st_ref_set(x_3, x_51, x_38);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
lean_inc(x_55);
x_56 = l_Lean_Elab_Command_isDefLike(x_55);
x_57 = lean_ctor_get_uint8(x_28, sizeof(void*)*8);
lean_dec(x_28);
x_58 = lean_box(x_57);
lean_inc(x_3);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lam__1___boxed), 4, 2);
lean_closure_set(x_59, 0, x_3);
lean_closure_set(x_59, 1, x_58);
if (x_56 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc(x_55);
x_60 = l_Lean_Syntax_getKind(x_55);
x_61 = lean_box(1);
x_62 = lean_mk_string_unchecked("Lean", 4, 4);
x_63 = lean_mk_string_unchecked("Parser", 6, 6);
x_64 = lean_mk_string_unchecked("Command", 7, 7);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_1, x_65);
lean_dec(x_1);
x_75 = lean_mk_string_unchecked("axiom", 5, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_76 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_75);
x_77 = lean_name_eq(x_60, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
x_67 = x_53;
x_68 = x_59;
x_69 = x_56;
goto block_74;
}
else
{
x_67 = x_53;
x_68 = x_59;
x_69 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_box(x_69);
x_71 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lam__2___boxed), 10, 7);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_66);
lean_closure_set(x_71, 2, x_55);
lean_closure_set(x_71, 3, x_62);
lean_closure_set(x_71, 4, x_63);
lean_closure_set(x_71, 5, x_64);
lean_closure_set(x_71, 6, x_60);
x_72 = lean_unbox(x_61);
x_73 = l_Lean_Elab_Command_withoutCommandIncrementality___redArg(x_72, x_71, x_2, x_3, x_67);
x_5 = x_68;
x_6 = x_73;
goto block_23;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_55);
x_78 = lean_mk_empty_array_with_capacity(x_54);
x_79 = lean_array_push(x_78, x_1);
x_80 = l_Lean_Elab_Command_elabMutualDef(x_79, x_2, x_3, x_53);
lean_dec(x_3);
x_5 = x_59;
x_6 = x_80;
goto block_23;
}
block_23:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_apply_2(x_5, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
else
{
lean_dec(x_7);
return x_10;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_5, x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_dec(x_15);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabDeclaration___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Command_elabDeclaration___lam__1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Command_elabDeclaration___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabDeclaration", 15, 15);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabDeclaration", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(206u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(226u);
x_11 = lean_unsigned_to_nat(41u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(19u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabDeclaration", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Lean_Elab_addBuiltinIncrementalElab(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_box(1);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Syntax_getArg(x_7, x_5);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_isDefLike(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_unbox(x_6);
return x_10;
}
else
{
if (x_4 == 0)
{
size_t x_11; size_t x_12; 
x_11 = lean_usize_of_nat(x_5);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_6);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_4);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_usize_of_nat(x_5);
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0(x_4, x_10, x_11);
lean_dec(x_4);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Command", 7, 7);
x_20 = lean_mk_string_unchecked("variable", 8, 8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_name_eq(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_mk_string_unchecked("universe", 8, 8);
x_24 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_23);
x_25 = lean_name_eq(x_2, x_24);
lean_dec(x_24);
x_3 = x_25;
goto block_16;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_3 = x_22;
goto block_16;
}
block_16:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Command", 7, 7);
x_7 = lean_mk_string_unchecked("check", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_10);
x_12 = lean_name_eq(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("open", 4, 4);
x_14 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_13);
x_15 = lean_name_eq(x_2, x_14);
lean_dec(x_14);
lean_dec(x_2);
return x_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Array_toSubarray___redArg(x_1, x_8, x_2);
x_11 = l_Array_ofSubarray___redArg(x_10);
lean_dec(x_10);
x_12 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
x_13 = l_Array_ofSubarray___redArg(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_name_eq(x_5, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_6, x_8);
x_12 = l_Lean_Name_append(x_5, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Name_components(x_1);
x_7 = l_Lean_Name_components(x_4);
x_8 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_6, x_7);
lean_dec(x_7);
x_1 = x_8;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Elab_Command_findCommonPrefix_go(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_1, x_3);
x_17 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_16, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Macro_throwUnsupported(lean_box(0), x_5, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_push(x_4, x_27);
x_7 = x_28;
x_8 = x_26;
goto block_13;
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_4, x_3, x_10);
lean_inc(x_9);
x_20 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_21 = lean_mk_string_unchecked("Lean.Elab.Declaration", 21, 21);
x_22 = lean_mk_string_unchecked("Lean.Elab.Command.expandMutualNamespace", 39, 39);
x_23 = lean_unsigned_to_nat(239u);
x_24 = lean_unsigned_to_nat(40u);
x_25 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_5);
x_27 = l_panic___at_____private_Lean_Elab_Do_0__Lean_Elab_Term_Do_destructTuple_destruct_spec__0(x_26, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_12 = x_28;
x_13 = x_29;
goto block_19;
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = l_Lean_extractMacroScopes(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = l_Lean_Name_replacePrefix(x_36, x_1, x_37);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 3);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
x_43 = l_Lean_MacroScopesView_review(x_42);
x_44 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_9, x_43);
x_12 = x_44;
x_13 = x_6;
goto block_19;
}
block_19:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_11, x_3, x_12);
x_3 = x_16;
x_4 = x_17;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_size(x_8);
x_10 = lean_usize_of_nat(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0(x_8, x_9, x_10, x_5, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_to_list(x_12);
x_15 = l_Lean_Elab_Command_findCommonPrefix(x_14);
x_16 = l_Lean_Name_isAnonymous(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_2);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1(x_15, x_9, x_10, x_8, x_2, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_box(2);
lean_inc(x_21);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_19);
lean_inc(x_1);
x_24 = l_Lean_Syntax_setArg(x_1, x_6, x_23);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_SourceInfo_fromRef(x_25, x_16);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_29 = lean_mk_string_unchecked("Command", 7, 7);
x_30 = lean_mk_string_unchecked("namespace", 9, 9);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
lean_inc(x_26);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_mkIdentFrom(x_1, x_15, x_16);
lean_dec(x_1);
lean_inc(x_33);
lean_inc(x_26);
x_34 = l_Lean_Syntax_node2(x_26, x_31, x_32, x_33);
x_35 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_35);
x_36 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_35);
lean_inc(x_26);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_35);
lean_inc(x_21);
lean_inc(x_26);
x_38 = l_Lean_Syntax_node1(x_26, x_21, x_33);
lean_inc(x_26);
x_39 = l_Lean_Syntax_node2(x_26, x_36, x_37, x_38);
x_40 = l_Lean_Syntax_node3(x_26, x_21, x_34, x_24, x_39);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_mk_string_unchecked("null", 4, 4);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = lean_box(2);
lean_inc(x_44);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_41);
lean_inc(x_1);
x_47 = l_Lean_Syntax_setArg(x_1, x_6, x_46);
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_SourceInfo_fromRef(x_48, x_16);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Parser", 6, 6);
x_52 = lean_mk_string_unchecked("Command", 7, 7);
x_53 = lean_mk_string_unchecked("namespace", 9, 9);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
lean_inc(x_49);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_mkIdentFrom(x_1, x_15, x_16);
lean_dec(x_1);
lean_inc(x_56);
lean_inc(x_49);
x_57 = l_Lean_Syntax_node2(x_49, x_54, x_55, x_56);
x_58 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_58);
x_59 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_58);
lean_inc(x_49);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_58);
lean_inc(x_44);
lean_inc(x_49);
x_61 = l_Lean_Syntax_node1(x_49, x_44, x_56);
lean_inc(x_49);
x_62 = l_Lean_Syntax_node2(x_49, x_59, x_60, x_61);
x_63 = l_Lean_Syntax_node3(x_49, x_44, x_57, x_47, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_42);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_17);
if (x_65 == 0)
{
return x_17;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_17, 0);
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_1);
x_69 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_13);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(1);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
return x_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualNamespace_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_expandMutualNamespace_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandMutualNamespace", 21, 21);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualNamespace), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandMutualNamespace", 21, 21);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(295u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(310u);
x_11 = lean_unsigned_to_nat(38u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(25u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_array_uget(x_1, x_3);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Command", 7, 7);
x_22 = lean_mk_string_unchecked("declaration", 11, 11);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
lean_inc(x_16);
x_24 = l_Lean_Syntax_isOfKind(x_16, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_inc(x_5);
lean_inc(x_16);
x_25 = l_Lean_Macro_expandMacro_x3f(x_16, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_push(x_17, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_7 = x_29;
x_8 = x_27;
goto block_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_16);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_array_push(x_17, x_31);
x_33 = lean_box(x_14);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_7 = x_34;
x_8 = x_30;
goto block_13;
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_16);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_18);
x_7 = x_39;
x_8 = x_6;
goto block_13;
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_array_size(x_9);
x_12 = lean_usize_of_nat(x_4);
lean_inc(x_2);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0(x_9, x_11, x_12, x_10, x_2, x_3);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_1);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_17);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_mk_string_unchecked("null", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_box(2);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
x_26 = l_Lean_Syntax_setArg(x_1, x_7, x_25);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_28);
x_33 = l_Lean_Syntax_setArg(x_1, x_7, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_expandMutualElement_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandMutualElement", 19, 19);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualElement), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandMutualElement", 19, 19);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(313u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(327u);
x_11 = lean_unsigned_to_nat(26u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(23u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_SourceInfo_fromRef(x_13, x_15);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Command", 7, 7);
x_20 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
lean_inc(x_16);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_16);
x_22 = lean_mk_string_unchecked("null", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = l_Array_mkArray0(lean_box(0));
lean_inc(x_23);
lean_inc(x_16);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_25);
lean_inc(x_16);
x_26 = l_Lean_Syntax_node2(x_16, x_21, x_9, x_25);
x_27 = lean_box(2);
lean_inc(x_23);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_12);
x_29 = l_Lean_Syntax_setArg(x_1, x_4, x_28);
x_30 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_30);
x_31 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_30);
lean_inc(x_16);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Syntax_node2(x_16, x_31, x_32, x_25);
x_34 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_34);
x_35 = lean_array_push(x_34, x_26);
x_36 = l_Array_append(lean_box(0), x_35, x_11);
lean_dec(x_11);
lean_inc(x_34);
x_37 = lean_array_push(x_34, x_29);
x_38 = l_Array_append(lean_box(0), x_36, x_37);
lean_dec(x_37);
x_39 = lean_array_push(x_34, x_33);
x_40 = l_Array_append(lean_box(0), x_38, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_ctor_get(x_2, 5);
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_SourceInfo_fromRef(x_45, x_47);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_mk_string_unchecked("Command", 7, 7);
x_52 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
lean_inc(x_48);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Array_mkArray0(lean_box(0));
lean_inc(x_56);
lean_inc(x_48);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_58);
lean_inc(x_48);
x_59 = l_Lean_Syntax_node2(x_48, x_53, x_54, x_58);
x_60 = lean_box(2);
lean_inc(x_56);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_44);
x_62 = l_Lean_Syntax_setArg(x_1, x_4, x_61);
x_63 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_63);
x_64 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_63);
lean_inc(x_48);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Syntax_node2(x_48, x_64, x_65, x_58);
x_67 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_67);
x_68 = lean_array_push(x_67, x_59);
x_69 = l_Array_append(lean_box(0), x_68, x_43);
lean_dec(x_43);
lean_inc(x_67);
x_70 = lean_array_push(x_67, x_62);
x_71 = l_Array_append(lean_box(0), x_69, x_70);
lean_dec(x_70);
x_72 = lean_array_push(x_67, x_66);
x_73 = l_Array_append(lean_box(0), x_71, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_56);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandMutualPreamble(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandMutualPreamble", 20, 20);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualPreamble___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandMutualPreamble", 20, 20);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(330u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(337u);
x_11 = lean_unsigned_to_nat(74u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(24u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_inductiveElabAttr;
x_9 = l_Lean_Syntax_getKind(x_1);
x_10 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_8, x_7, x_9);
lean_dec(x_9);
x_11 = l_List_isEmpty___redArg(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(1);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_inductiveElabAttr;
x_18 = l_Lean_Syntax_getKind(x_1);
x_19 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_17, x_16, x_18);
lean_dec(x_18);
x_20 = l_List_isEmpty___redArg(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_box(1);
x_17 = lean_array_uget(x_1, x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg(x_19, x_5, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_9 = x_7;
x_10 = x_27;
goto block_16;
}
block_16:
{
if (x_9 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_5 = x_4;
goto block_8;
}
else
{
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_5 = x_4;
goto block_8;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_usize_of_nat(x_12);
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1(x_11, x_15, x_16, x_2, x_3, x_4);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_5 = x_20;
goto block_8;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("invalid mutual block: either all elements of the block must be inductive/structure declarations, or they must all be definitions/theorems/abbrevs", 145, 145);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_10, x_2, x_3, x_8);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Lean_Elab_Command_elabMutualInductive(x_15, x_2, x_3, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Elab_Command_withoutCommandIncrementality___redArg(x_8, x_6, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = l_Lean_Elab_Command_elabMutualDef(x_12, x_2, x_3, x_4);
lean_dec(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_isInductiveCommand___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_isMutualInductive___at___Lean_Elab_Command_elabMutual_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabMutual___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("mutual", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabMutual", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabMutual", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(340u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(348u);
x_11 = lean_unsigned_to_nat(154u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(14u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabMutual", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Lean_Elab_addBuiltinIncrementalElab(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
lean_inc(x_17);
x_20 = l_Lean_Syntax_getKind(x_17);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Parser", 6, 6);
x_23 = lean_mk_string_unchecked("Command", 7, 7);
x_24 = lean_mk_string_unchecked("eraseAttr", 9, 9);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_26 = lean_name_eq(x_20, x_25);
lean_dec(x_25);
lean_dec(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_array_push(x_18, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_8 = x_28;
x_9 = x_7;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_st_ref_get(x_6, x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Lean_Syntax_getArg(x_17, x_29);
x_35 = l_Lean_Syntax_getId(x_34);
lean_dec(x_34);
x_36 = lean_erase_macro_scopes(x_35);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_isAttribute(x_37, x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_mk_string_unchecked("unknown attribute [", 19, 19);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_MessageData_ofName(x_36);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_41);
lean_ctor_set(x_30, 0, x_40);
x_42 = lean_mk_string_unchecked("]", 1, 1);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_5);
x_45 = l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(x_17, x_44, x_5, x_6, x_33);
lean_dec(x_17);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
lean_ctor_set(x_45, 1, x_19);
lean_ctor_set(x_45, 0, x_18);
x_8 = x_45;
x_9 = x_47;
goto block_14;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_19);
x_8 = x_50;
x_9 = x_49;
goto block_14;
}
}
else
{
lean_object* x_51; 
lean_dec(x_17);
x_51 = lean_array_push(x_19, x_36);
lean_ctor_set(x_30, 1, x_51);
lean_ctor_set(x_30, 0, x_18);
x_8 = x_30;
x_9 = x_33;
goto block_14;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_54 = l_Lean_Syntax_getArg(x_17, x_29);
x_55 = l_Lean_Syntax_getId(x_54);
lean_dec(x_54);
x_56 = lean_erase_macro_scopes(x_55);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = l_Lean_isAttribute(x_57, x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_mk_string_unchecked("unknown attribute [", 19, 19);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = l_Lean_MessageData_ofName(x_56);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("]", 1, 1);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_5);
x_66 = l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(x_17, x_65, x_5, x_6, x_53);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_19);
x_8 = x_69;
x_9 = x_67;
goto block_14;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_17);
x_70 = lean_array_push(x_19, x_56);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_18);
lean_ctor_set(x_71, 1, x_70);
x_8 = x_71;
x_9 = x_53;
goto block_14;
}
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
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_8(x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0___boxed), 9, 0);
x_10 = lean_alloc_closure((void*)(l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__1), 11, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_15 = l_instMonadEIO(lean_box(0));
x_16 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_30);
lean_inc(x_27);
lean_inc(x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_24);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_27);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_30);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_40);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_53, 0, x_40);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_55, 0, x_42);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_44);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
x_61 = lean_box(0);
x_62 = l_instInhabitedOfMonad___redArg(x_60, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_7(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_64;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
x_11 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
x_12 = lean_unsigned_to_nat(367u);
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
x_22 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
lean_inc(x_1);
x_26 = l_Lean_Syntax_formatStx(x_1, x_23, x_25);
x_27 = lean_unsigned_to_nat(120u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_format_pretty(x_26, x_27, x_28, x_28);
x_30 = lean_string_append(x_22, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(x_2, x_33);
x_35 = l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_32, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_12 = l_Lean_Attribute_erase(x_1, x_11, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_5 = x_14;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_MessageData_ofConstName(x_1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwUnknownIdentifier___at___Lean_Elab_Term_resolveName_process_spec__0(lean_box(0), x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_34; lean_object* x_42; 
lean_inc(x_12);
lean_inc(x_1);
x_42 = l_Lean_Elab_realizeGlobalConstWithInfos(x_1, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_dec(x_6);
x_34 = x_42;
goto block_41;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_59; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_59 = l_Lean_Exception_isInterrupt(x_43);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Exception_isRuntime(x_43);
lean_dec(x_43);
x_45 = x_60;
goto block_58;
}
else
{
lean_dec(x_43);
x_45 = x_59;
goto block_58;
}
block_58:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_42);
x_46 = l_Lean_Syntax_getId(x_1);
x_47 = lean_erase_macro_scopes(x_46);
x_48 = l_Lean_Meta_Simp_isBuiltinSimproc(x_47, x_11, x_12, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
lean_inc(x_7);
x_52 = l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg(x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
x_34 = x_52;
goto block_41;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 1);
x_55 = lean_ctor_get(x_48, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 1, x_6);
lean_ctor_set(x_48, 0, x_47);
x_14 = x_48;
x_15 = x_54;
goto block_33;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_6);
x_14 = x_57;
x_15 = x_56;
goto block_33;
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_6);
x_34 = x_42;
goto block_41;
}
}
}
block_33:
{
lean_object* x_16; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1(x_1, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_applyAttributes(x_17, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
lean_inc(x_4);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg(x_17, x_3, x_21, x_23, x_4, x_11, x_12, x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_4);
return x_24;
}
}
else
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
return x_19;
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_41:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_14 = x_35;
x_15 = x_36;
goto block_33;
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_12 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_array_uget(x_3, x_5);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0___boxed), 13, 6);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_16);
lean_closure_set(x_19, 5, x_15);
x_20 = l_Lean_replaceRef(x_18, x_13);
lean_dec(x_13);
lean_dec(x_18);
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_30 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_27);
lean_ctor_set(x_30, 8, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*9, x_29);
x_31 = l_Lean_Elab_Command_liftTermElabM___redArg(x_19, x_30, x_8, x_14);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_add(x_5, x_34);
x_5 = x_35;
x_6 = x_17;
x_9 = x_32;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_12 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_array_uget(x_3, x_5);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0___boxed), 13, 6);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_16);
lean_closure_set(x_19, 5, x_15);
x_20 = l_Lean_replaceRef(x_18, x_13);
lean_dec(x_13);
lean_dec(x_18);
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_30 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_27);
lean_ctor_set(x_30, 8, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*9, x_29);
x_31 = l_Lean_Elab_Command_liftTermElabM___redArg(x_19, x_30, x_8, x_14);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_add(x_5, x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5(x_1, x_2, x_3, x_4, x_35, x_17, x_7, x_8, x_32);
return x_36;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getSepArgs(x_8);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_array_size(x_9);
x_12 = lean_usize_of_nat(x_5);
lean_inc(x_2);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0(x_9, x_11, x_12, x_10, x_2, x_3, x_4);
lean_dec(x_9);
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
lean_inc(x_2);
x_18 = l_Lean_Elab_elabAttrs___at___Lean_Elab_elabDeclAttrs___at___Lean_Elab_elabModifiers___at___Lean_Elab_Command_elabMutualInductive_spec__0_spec__0_spec__0(x_16, x_2, x_3, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_array_size(x_23);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5(x_19, x_17, x_23, x_25, x_12, x_24, x_2, x_3, x_20);
lean_dec(x_2);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
return x_26;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___Lean_ensureNonAmbiguous___at___Lean_Elab_Command_elabAttr_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___Lean_Elab_Command_elabAttr_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5_spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabAttr_spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAttr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("attribute", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabAttr", 8, 8);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAttr___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabAttr", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(351u);
x_8 = lean_unsigned_to_nat(36u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(383u);
x_11 = lean_unsigned_to_nat(39u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(40u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Syntax_getRange_x3f(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_DeclarationRange_ofStringPositions(x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
lean_ctor_set(x_6, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_DeclarationRange_ofStringPositions(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_declRangeExt;
x_10 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_9, x_8, x_1, x_2);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 8);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_ref_set(x_3, x_19, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_7 = l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(x_2, x_4, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(x_3, x_4, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_inc(x_16);
x_21 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_21 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg(x_1, x_22, x_5, x_19);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_7 = l_Lean_Syntax_getKind(x_3);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = lean_mk_string_unchecked("example", 7, 7);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = lean_name_eq(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_2);
lean_inc(x_3);
x_17 = lean_array_push(x_16, x_3);
x_18 = lean_mk_string_unchecked("null", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(2);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_17);
x_22 = l_Lean_Elab_getDeclarationSelectionRef(x_3);
x_23 = l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0(x_1, x_21, x_22, x_4, x_5, x_6);
lean_dec(x_22);
lean_dec(x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("initialize", 10, 10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_192; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_14);
lean_inc(x_13);
x_192 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_193 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_194 = lean_unsigned_to_nat(1u);
x_195 = l_Lean_Syntax_getArg(x_1, x_194);
x_196 = lean_mk_string_unchecked("initializeKeyword", 17, 17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_197 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_196);
lean_inc(x_195);
x_198 = l_Lean_Syntax_isOfKind(x_195, x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_254; 
lean_dec(x_195);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_254 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_254;
}
else
{
lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_564; uint8_t x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_697; uint8_t x_698; 
x_255 = lean_unsigned_to_nat(2u);
x_697 = l_Lean_Syntax_getArg(x_1, x_255);
x_698 = l_Lean_Syntax_isNone(x_697);
if (x_698 == 0)
{
lean_object* x_699; uint8_t x_700; 
x_699 = lean_unsigned_to_nat(3u);
lean_inc(x_697);
x_700 = l_Lean_Syntax_matchesNull(x_697, x_699);
if (x_700 == 0)
{
lean_object* x_701; 
lean_dec(x_697);
lean_dec(x_195);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_701 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_701;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; uint8_t x_706; 
x_702 = l_Lean_Syntax_getArg(x_697, x_194);
x_703 = lean_mk_string_unchecked("Term", 4, 4);
x_704 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
x_705 = l_Lean_Name_mkStr4(x_5, x_6, x_703, x_704);
lean_inc(x_702);
x_706 = l_Lean_Syntax_isOfKind(x_702, x_705);
lean_dec(x_705);
if (x_706 == 0)
{
lean_object* x_707; 
lean_dec(x_702);
lean_dec(x_697);
lean_dec(x_195);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_707 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = l_Lean_Syntax_getArg(x_702, x_194);
lean_dec(x_702);
x_709 = l_Lean_Syntax_getArg(x_697, x_12);
lean_dec(x_697);
x_710 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_710, 0, x_709);
x_711 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_711, 0, x_708);
x_682 = x_710;
x_683 = x_711;
x_684 = x_2;
x_685 = x_3;
x_686 = x_4;
goto block_696;
}
}
}
else
{
lean_object* x_712; 
lean_dec(x_697);
x_712 = lean_box(0);
x_682 = x_712;
x_683 = x_712;
x_684 = x_2;
x_685 = x_3;
x_686 = x_4;
goto block_696;
}
block_310:
{
lean_object* x_265; uint8_t x_266; 
x_265 = l_Lean_Syntax_getArg(x_13, x_194);
x_266 = l_Lean_Syntax_matchesNull(x_265, x_12);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_267 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_268 = l_Lean_stringToMessageData(x_267);
lean_dec(x_267);
x_269 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_268, x_262, x_263, x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_13);
return x_269;
}
else
{
lean_object* x_270; uint8_t x_271; 
x_270 = l_Lean_Syntax_getArg(x_13, x_255);
x_271 = l_Lean_Syntax_matchesNull(x_270, x_12);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_272 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_273 = l_Lean_stringToMessageData(x_272);
lean_dec(x_272);
x_274 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_273, x_262, x_263, x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_13);
return x_274;
}
else
{
lean_object* x_275; uint8_t x_276; 
x_275 = l_Lean_Syntax_getArg(x_13, x_257);
x_276 = l_Lean_Syntax_matchesNull(x_275, x_12);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_277 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_278 = l_Lean_stringToMessageData(x_277);
lean_dec(x_277);
x_279 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_278, x_262, x_263, x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_13);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = lean_unsigned_to_nat(4u);
x_281 = l_Lean_Syntax_getArg(x_13, x_280);
x_282 = l_Lean_Syntax_matchesNull(x_281, x_12);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_283 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_284 = l_Lean_stringToMessageData(x_283);
lean_dec(x_283);
x_285 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_284, x_262, x_263, x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_13);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = lean_unsigned_to_nat(5u);
x_287 = l_Lean_Syntax_getArg(x_13, x_286);
x_288 = l_Lean_Syntax_matchesNull(x_287, x_12);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_289 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_290 = l_Lean_stringToMessageData(x_289);
lean_dec(x_289);
x_291 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_290, x_262, x_263, x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_13);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_13);
x_292 = l_Lean_Elab_Command_getRef(x_262, x_263, x_264);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lean_Elab_Command_getCurrMacroScope(x_262, x_263, x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Lean_Elab_Command_getMainModule___redArg(x_263, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = l_Lean_SourceInfo_fromRef(x_293, x_256);
lean_dec(x_293);
x_302 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_303 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_302);
x_304 = lean_mk_string_unchecked("null", 4, 4);
x_305 = l_Lean_Name_mkStr1(x_304);
x_306 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_307; 
x_307 = l_Array_empty(lean_box(0));
x_16 = x_305;
x_17 = x_303;
x_18 = x_300;
x_19 = x_296;
x_20 = x_259;
x_21 = x_299;
x_22 = x_256;
x_23 = x_263;
x_24 = x_306;
x_25 = x_301;
x_26 = x_262;
x_27 = x_258;
x_28 = x_260;
x_29 = x_307;
goto block_115;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_261, 0);
lean_inc(x_308);
lean_dec(x_261);
x_309 = l_Array_mkArray1___redArg(x_308);
x_16 = x_305;
x_17 = x_303;
x_18 = x_300;
x_19 = x_296;
x_20 = x_259;
x_21 = x_299;
x_22 = x_256;
x_23 = x_263;
x_24 = x_306;
x_25 = x_301;
x_26 = x_262;
x_27 = x_258;
x_28 = x_260;
x_29 = x_309;
goto block_115;
}
}
}
}
}
}
}
block_337:
{
if (x_192 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_319 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
x_321 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_320, x_316, x_317, x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_13);
return x_321;
}
else
{
lean_object* x_322; uint8_t x_323; 
x_322 = l_Lean_Syntax_getArg(x_13, x_12);
x_323 = l_Lean_Syntax_isNone(x_322);
if (x_323 == 0)
{
uint8_t x_324; 
lean_inc(x_322);
x_324 = l_Lean_Syntax_matchesNull(x_322, x_194);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_322);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_325 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_326 = l_Lean_stringToMessageData(x_325);
lean_dec(x_325);
x_327 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_326, x_316, x_317, x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_13);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = l_Lean_Syntax_getArg(x_322, x_12);
lean_dec(x_322);
x_329 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_330 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_329);
lean_inc(x_328);
x_331 = l_Lean_Syntax_isOfKind(x_328, x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_328);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_332 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_333 = l_Lean_stringToMessageData(x_332);
lean_dec(x_332);
x_334 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_333, x_316, x_317, x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_13);
return x_334;
}
else
{
lean_object* x_335; 
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_328);
x_256 = x_311;
x_257 = x_312;
x_258 = x_314;
x_259 = x_313;
x_260 = x_315;
x_261 = x_335;
x_262 = x_316;
x_263 = x_317;
x_264 = x_318;
goto block_310;
}
}
}
else
{
lean_object* x_336; 
lean_dec(x_322);
x_336 = lean_box(0);
x_256 = x_311;
x_257 = x_312;
x_258 = x_314;
x_259 = x_313;
x_260 = x_315;
x_261 = x_336;
x_262 = x_316;
x_263 = x_317;
x_264 = x_318;
goto block_310;
}
}
}
block_422:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
lean_inc(x_357);
x_359 = l_Array_append(lean_box(0), x_357, x_358);
lean_dec(x_358);
x_360 = lean_mk_string_unchecked("opaque", 6, 6);
x_361 = lean_mk_string_unchecked("declId", 6, 6);
x_362 = lean_mk_empty_array_with_capacity(x_12);
x_363 = lean_box(2);
lean_inc(x_340);
x_364 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_340);
lean_ctor_set(x_364, 2, x_362);
x_365 = lean_mk_empty_array_with_capacity(x_255);
lean_inc(x_344);
x_366 = lean_array_push(x_365, x_344);
x_367 = lean_array_push(x_366, x_364);
x_368 = lean_mk_string_unchecked("declSig", 7, 7);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_369 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_368);
x_370 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_352);
lean_inc(x_6);
lean_inc(x_5);
x_371 = l_Lean_Name_mkStr4(x_5, x_6, x_352, x_370);
x_372 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_372);
lean_inc(x_338);
x_373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_373, 0, x_338);
lean_ctor_set(x_373, 1, x_372);
lean_inc(x_339);
lean_inc(x_371);
lean_inc(x_338);
x_374 = l_Lean_Syntax_node2(x_338, x_371, x_373, x_339);
x_375 = l_Lean_Elab_Command_getScope___redArg(x_348, x_347);
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_377 = lean_ctor_get(x_375, 0);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_340);
lean_inc(x_338);
x_379 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_379, 0, x_338);
lean_ctor_set(x_379, 1, x_340);
lean_ctor_set(x_379, 2, x_359);
lean_inc(x_360);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_380 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_360);
lean_inc(x_338);
lean_ctor_set_tag(x_375, 2);
lean_ctor_set(x_375, 1, x_360);
lean_ctor_set(x_375, 0, x_338);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_381 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_361);
lean_inc(x_381);
x_382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_382, 0, x_363);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set(x_382, 2, x_367);
lean_inc(x_353);
lean_inc(x_338);
x_383 = l_Lean_Syntax_node2(x_338, x_369, x_353, x_374);
lean_inc_n(x_353, 3);
lean_inc(x_15);
lean_inc(x_338);
x_384 = l_Lean_Syntax_node6(x_338, x_15, x_342, x_341, x_379, x_353, x_353, x_353);
lean_inc(x_338);
x_385 = l_Lean_Syntax_node4(x_338, x_380, x_375, x_382, x_383, x_353);
lean_inc(x_354);
x_386 = l_Lean_Syntax_node2(x_338, x_354, x_384, x_385);
x_387 = lean_ctor_get(x_377, 2);
lean_inc(x_387);
lean_dec(x_377);
x_388 = l_Lean_Syntax_getId(x_344);
lean_dec(x_344);
x_389 = l_Lean_Name_append(x_387, x_388);
if (lean_obj_tag(x_350) == 0)
{
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_381;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_386;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_389;
x_215 = x_349;
x_216 = x_348;
x_217 = x_378;
goto block_253;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_390 = lean_ctor_get(x_350, 0);
lean_inc(x_390);
lean_dec(x_350);
x_391 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_392 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_391);
x_393 = l_Lean_Syntax_isOfKind(x_390, x_392);
lean_dec(x_392);
if (x_393 == 0)
{
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_381;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_386;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_389;
x_215 = x_349;
x_216 = x_348;
x_217 = x_378;
goto block_253;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = lean_st_ref_get(x_348, x_378);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_ctor_get(x_395, 0);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_mkPrivateName(x_397, x_389);
lean_dec(x_397);
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_381;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_386;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_398;
x_215 = x_349;
x_216 = x_348;
x_217 = x_396;
goto block_253;
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_399 = lean_ctor_get(x_375, 0);
x_400 = lean_ctor_get(x_375, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_375);
lean_inc(x_340);
lean_inc(x_338);
x_401 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_401, 0, x_338);
lean_ctor_set(x_401, 1, x_340);
lean_ctor_set(x_401, 2, x_359);
lean_inc(x_360);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_402 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_360);
lean_inc(x_338);
x_403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_403, 0, x_338);
lean_ctor_set(x_403, 1, x_360);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_404 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_361);
lean_inc(x_404);
x_405 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_405, 0, x_363);
lean_ctor_set(x_405, 1, x_404);
lean_ctor_set(x_405, 2, x_367);
lean_inc(x_353);
lean_inc(x_338);
x_406 = l_Lean_Syntax_node2(x_338, x_369, x_353, x_374);
lean_inc_n(x_353, 3);
lean_inc(x_15);
lean_inc(x_338);
x_407 = l_Lean_Syntax_node6(x_338, x_15, x_342, x_341, x_401, x_353, x_353, x_353);
lean_inc(x_338);
x_408 = l_Lean_Syntax_node4(x_338, x_402, x_403, x_405, x_406, x_353);
lean_inc(x_354);
x_409 = l_Lean_Syntax_node2(x_338, x_354, x_407, x_408);
x_410 = lean_ctor_get(x_399, 2);
lean_inc(x_410);
lean_dec(x_399);
x_411 = l_Lean_Syntax_getId(x_344);
lean_dec(x_344);
x_412 = l_Lean_Name_append(x_410, x_411);
if (lean_obj_tag(x_350) == 0)
{
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_404;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_409;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_412;
x_215 = x_349;
x_216 = x_348;
x_217 = x_400;
goto block_253;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_413 = lean_ctor_get(x_350, 0);
lean_inc(x_413);
lean_dec(x_350);
x_414 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_415 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_414);
x_416 = l_Lean_Syntax_isOfKind(x_413, x_415);
lean_dec(x_415);
if (x_416 == 0)
{
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_404;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_409;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_412;
x_215 = x_349;
x_216 = x_348;
x_217 = x_400;
goto block_253;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_417 = lean_st_ref_get(x_348, x_400);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_418, 0);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_mkPrivateName(x_420, x_412);
lean_dec(x_420);
x_199 = x_339;
x_200 = x_340;
x_201 = x_343;
x_202 = x_404;
x_203 = x_371;
x_204 = x_345;
x_205 = x_372;
x_206 = x_346;
x_207 = x_409;
x_208 = x_351;
x_209 = x_352;
x_210 = x_354;
x_211 = x_356;
x_212 = x_357;
x_213 = x_355;
x_214 = x_421;
x_215 = x_349;
x_216 = x_348;
x_217 = x_419;
goto block_253;
}
}
}
}
block_456:
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_446 = l_Array_append(lean_box(0), x_429, x_445);
lean_dec(x_445);
lean_inc(x_425);
lean_inc(x_423);
x_447 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_447, 0, x_423);
lean_ctor_set(x_447, 1, x_425);
lean_ctor_set(x_447, 2, x_446);
x_448 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_423);
x_449 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_449, 0, x_423);
lean_ctor_set(x_449, 1, x_448);
lean_inc(x_423);
x_450 = l_Lean_Syntax_node3(x_423, x_428, x_437, x_447, x_449);
lean_inc(x_425);
lean_inc(x_423);
x_451 = l_Lean_Syntax_node1(x_423, x_425, x_450);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_452; 
x_452 = l_Array_empty(lean_box(0));
x_338 = x_423;
x_339 = x_424;
x_340 = x_425;
x_341 = x_451;
x_342 = x_426;
x_343 = x_427;
x_344 = x_430;
x_345 = x_431;
x_346 = x_432;
x_347 = x_433;
x_348 = x_434;
x_349 = x_436;
x_350 = x_435;
x_351 = x_438;
x_352 = x_439;
x_353 = x_441;
x_354 = x_440;
x_355 = x_444;
x_356 = x_443;
x_357 = x_442;
x_358 = x_452;
goto block_422;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_435, 0);
lean_inc(x_453);
x_454 = l_Array_empty(lean_box(0));
x_455 = lean_array_push(x_454, x_453);
x_338 = x_423;
x_339 = x_424;
x_340 = x_425;
x_341 = x_451;
x_342 = x_426;
x_343 = x_427;
x_344 = x_430;
x_345 = x_431;
x_346 = x_432;
x_347 = x_433;
x_348 = x_434;
x_349 = x_436;
x_350 = x_435;
x_351 = x_438;
x_352 = x_439;
x_353 = x_441;
x_354 = x_440;
x_355 = x_444;
x_356 = x_443;
x_357 = x_442;
x_358 = x_455;
goto block_422;
}
}
block_506:
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_inc(x_474);
x_476 = l_Array_append(lean_box(0), x_474, x_475);
lean_dec(x_475);
lean_inc(x_460);
lean_inc(x_458);
x_477 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_477, 0, x_458);
lean_ctor_set(x_477, 1, x_460);
lean_ctor_set(x_477, 2, x_476);
x_478 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_471);
lean_inc(x_6);
lean_inc(x_5);
x_479 = l_Lean_Name_mkStr4(x_5, x_6, x_471, x_478);
x_480 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_458);
x_481 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_481, 0, x_458);
lean_ctor_set(x_481, 1, x_480);
x_482 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_471);
lean_inc(x_6);
lean_inc(x_5);
x_483 = l_Lean_Name_mkStr4(x_5, x_6, x_471, x_482);
x_484 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_471);
lean_inc(x_6);
lean_inc(x_5);
x_485 = l_Lean_Name_mkStr4(x_5, x_6, x_471, x_484);
lean_inc(x_474);
lean_inc(x_460);
lean_inc(x_458);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_458);
lean_ctor_set(x_486, 1, x_460);
lean_ctor_set(x_486, 2, x_474);
lean_inc(x_486);
lean_inc(x_458);
x_487 = l_Lean_Syntax_node1(x_458, x_485, x_486);
x_488 = lean_mk_string_unchecked("Attr", 4, 4);
x_489 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
x_490 = l_Lean_Name_mkStr4(x_5, x_6, x_488, x_489);
x_491 = l_Lean_mkIdentFrom(x_1, x_461, x_463);
lean_dec(x_1);
x_492 = lean_mk_string_unchecked("initFn", 6, 6);
lean_inc(x_492);
x_493 = l_String_toSubstring_x27(x_492);
x_494 = l_Lean_Name_mkStr1(x_492);
lean_inc(x_494);
x_495 = l_Lean_addMacroScope(x_464, x_494, x_470);
x_496 = lean_box(0);
lean_inc(x_493);
lean_inc(x_458);
x_497 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_497, 0, x_458);
lean_ctor_set(x_497, 1, x_493);
lean_ctor_set(x_497, 2, x_495);
lean_ctor_set(x_497, 3, x_496);
lean_inc(x_460);
lean_inc(x_458);
x_498 = l_Lean_Syntax_node1(x_458, x_460, x_497);
lean_inc(x_458);
x_499 = l_Lean_Syntax_node2(x_458, x_490, x_491, x_498);
lean_inc(x_458);
x_500 = l_Lean_Syntax_node2(x_458, x_483, x_487, x_499);
x_501 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_458);
x_502 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_502, 0, x_458);
lean_ctor_set(x_502, 1, x_501);
x_503 = l_Array_mkArray2(lean_box(0), x_500, x_502);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_504; 
x_504 = l_Array_empty(lean_box(0));
x_423 = x_458;
x_424 = x_459;
x_425 = x_460;
x_426 = x_477;
x_427 = x_493;
x_428 = x_479;
x_429 = x_503;
x_430 = x_462;
x_431 = x_494;
x_432 = x_463;
x_433 = x_465;
x_434 = x_466;
x_435 = x_468;
x_436 = x_467;
x_437 = x_481;
x_438 = x_469;
x_439 = x_471;
x_440 = x_472;
x_441 = x_486;
x_442 = x_474;
x_443 = x_496;
x_444 = x_473;
x_445 = x_504;
goto block_456;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_457, 0);
lean_inc(x_505);
lean_dec(x_457);
x_423 = x_458;
x_424 = x_459;
x_425 = x_460;
x_426 = x_477;
x_427 = x_493;
x_428 = x_479;
x_429 = x_503;
x_430 = x_462;
x_431 = x_494;
x_432 = x_463;
x_433 = x_465;
x_434 = x_466;
x_435 = x_468;
x_436 = x_467;
x_437 = x_481;
x_438 = x_469;
x_439 = x_471;
x_440 = x_472;
x_441 = x_486;
x_442 = x_474;
x_443 = x_496;
x_444 = x_473;
x_445 = x_505;
goto block_456;
}
}
block_538:
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_520 = l_Lean_Elab_Command_getRef(x_512, x_511, x_510);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
x_523 = l_Lean_Elab_Command_getCurrMacroScope(x_512, x_511, x_522);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = l_Lean_Elab_Command_getMainModule___redArg(x_511, x_525);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = l_Lean_SourceInfo_fromRef(x_521, x_509);
lean_dec(x_521);
x_530 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_531 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_530);
x_532 = lean_mk_string_unchecked("null", 4, 4);
x_533 = l_Lean_Name_mkStr1(x_532);
x_534 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_535; 
x_535 = l_Array_empty(lean_box(0));
x_457 = x_508;
x_458 = x_529;
x_459 = x_507;
x_460 = x_533;
x_461 = x_516;
x_462 = x_515;
x_463 = x_509;
x_464 = x_527;
x_465 = x_528;
x_466 = x_511;
x_467 = x_512;
x_468 = x_519;
x_469 = x_513;
x_470 = x_524;
x_471 = x_514;
x_472 = x_531;
x_473 = x_518;
x_474 = x_534;
x_475 = x_535;
goto block_506;
}
else
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_517, 0);
lean_inc(x_536);
lean_dec(x_517);
x_537 = l_Array_mkArray1___redArg(x_536);
x_457 = x_508;
x_458 = x_529;
x_459 = x_507;
x_460 = x_533;
x_461 = x_516;
x_462 = x_515;
x_463 = x_509;
x_464 = x_527;
x_465 = x_528;
x_466 = x_511;
x_467 = x_512;
x_468 = x_519;
x_469 = x_513;
x_470 = x_524;
x_471 = x_514;
x_472 = x_531;
x_473 = x_518;
x_474 = x_534;
x_475 = x_537;
goto block_506;
}
}
block_563:
{
lean_object* x_552; lean_object* x_553; uint8_t x_554; 
x_552 = lean_unsigned_to_nat(5u);
x_553 = l_Lean_Syntax_getArg(x_13, x_552);
x_554 = l_Lean_Syntax_matchesNull(x_553, x_12);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_555 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_556 = l_Lean_stringToMessageData(x_555);
lean_dec(x_555);
x_557 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_556, x_549, x_550, x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_13);
return x_557;
}
else
{
lean_object* x_558; 
lean_dec(x_13);
x_558 = l_Lean_Syntax_getOptional_x3f(x_542);
lean_dec(x_542);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; 
x_559 = lean_box(0);
x_507 = x_541;
x_508 = x_540;
x_509 = x_539;
x_510 = x_551;
x_511 = x_550;
x_512 = x_549;
x_513 = x_548;
x_514 = x_545;
x_515 = x_544;
x_516 = x_543;
x_517 = x_547;
x_518 = x_546;
x_519 = x_559;
goto block_538;
}
else
{
uint8_t x_560; 
x_560 = !lean_is_exclusive(x_558);
if (x_560 == 0)
{
x_507 = x_541;
x_508 = x_540;
x_509 = x_539;
x_510 = x_551;
x_511 = x_550;
x_512 = x_549;
x_513 = x_548;
x_514 = x_545;
x_515 = x_544;
x_516 = x_543;
x_517 = x_547;
x_518 = x_546;
x_519 = x_558;
goto block_538;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_558, 0);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
x_507 = x_541;
x_508 = x_540;
x_509 = x_539;
x_510 = x_551;
x_511 = x_550;
x_512 = x_549;
x_513 = x_548;
x_514 = x_545;
x_515 = x_544;
x_516 = x_543;
x_517 = x_547;
x_518 = x_546;
x_519 = x_562;
goto block_538;
}
}
}
}
block_599:
{
lean_object* x_576; uint8_t x_577; 
x_576 = l_Lean_Syntax_getArg(x_13, x_566);
x_577 = l_Lean_Syntax_matchesNull(x_576, x_12);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_578 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_579 = l_Lean_stringToMessageData(x_578);
lean_dec(x_578);
x_580 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_579, x_573, x_574, x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_13);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; 
x_581 = l_Lean_Syntax_getArg(x_13, x_255);
x_582 = lean_unsigned_to_nat(4u);
x_583 = l_Lean_Syntax_getArg(x_13, x_582);
x_584 = l_Lean_Syntax_isNone(x_583);
if (x_584 == 0)
{
uint8_t x_585; 
lean_inc(x_583);
x_585 = l_Lean_Syntax_matchesNull(x_583, x_194);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_586 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_587 = l_Lean_stringToMessageData(x_586);
lean_dec(x_586);
x_588 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_587, x_573, x_574, x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_13);
return x_588;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_589 = l_Lean_Syntax_getArg(x_583, x_12);
lean_dec(x_583);
x_590 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_591 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_590);
lean_inc(x_589);
x_592 = l_Lean_Syntax_isOfKind(x_589, x_591);
lean_dec(x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_589);
lean_dec(x_581);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_593 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_594 = l_Lean_stringToMessageData(x_593);
lean_dec(x_593);
x_595 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_594, x_573, x_574, x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_13);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; 
x_596 = l_Lean_Syntax_getArg(x_589, x_12);
lean_dec(x_589);
x_597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_597, 0, x_596);
x_539 = x_565;
x_540 = x_572;
x_541 = x_564;
x_542 = x_581;
x_543 = x_569;
x_544 = x_568;
x_545 = x_567;
x_546 = x_571;
x_547 = x_570;
x_548 = x_597;
x_549 = x_573;
x_550 = x_574;
x_551 = x_575;
goto block_563;
}
}
}
else
{
lean_object* x_598; 
lean_dec(x_583);
x_598 = lean_box(0);
x_539 = x_565;
x_540 = x_572;
x_541 = x_564;
x_542 = x_581;
x_543 = x_569;
x_544 = x_568;
x_545 = x_567;
x_546 = x_571;
x_547 = x_570;
x_548 = x_598;
x_549 = x_573;
x_550 = x_574;
x_551 = x_575;
goto block_563;
}
}
}
block_628:
{
lean_object* x_611; uint8_t x_612; 
x_611 = l_Lean_Syntax_getArg(x_13, x_194);
x_612 = l_Lean_Syntax_isNone(x_611);
if (x_612 == 0)
{
uint8_t x_613; 
lean_inc(x_611);
x_613 = l_Lean_Syntax_matchesNull(x_611, x_194);
if (x_613 == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_611);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_601);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_614 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_615 = l_Lean_stringToMessageData(x_614);
lean_dec(x_614);
x_616 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_615, x_608, x_609, x_610);
lean_dec(x_609);
lean_dec(x_608);
lean_dec(x_13);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; 
x_617 = l_Lean_Syntax_getArg(x_611, x_12);
lean_dec(x_611);
x_618 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_605);
lean_inc(x_6);
lean_inc(x_5);
x_619 = l_Lean_Name_mkStr4(x_5, x_6, x_605, x_618);
lean_inc(x_617);
x_620 = l_Lean_Syntax_isOfKind(x_617, x_619);
lean_dec(x_619);
if (x_620 == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_617);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_601);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_621 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_622 = l_Lean_stringToMessageData(x_621);
lean_dec(x_621);
x_623 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_622, x_608, x_609, x_610);
lean_dec(x_609);
lean_dec(x_608);
lean_dec(x_13);
return x_623;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = l_Lean_Syntax_getArg(x_617, x_194);
lean_dec(x_617);
x_625 = l_Lean_Syntax_getArgs(x_624);
lean_dec(x_624);
x_626 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_626, 0, x_625);
x_564 = x_601;
x_565 = x_600;
x_566 = x_602;
x_567 = x_605;
x_568 = x_604;
x_569 = x_603;
x_570 = x_607;
x_571 = x_606;
x_572 = x_626;
x_573 = x_608;
x_574 = x_609;
x_575 = x_610;
goto block_599;
}
}
}
else
{
lean_object* x_627; 
lean_dec(x_611);
x_627 = lean_box(0);
x_564 = x_601;
x_565 = x_600;
x_566 = x_602;
x_567 = x_605;
x_568 = x_604;
x_569 = x_603;
x_570 = x_607;
x_571 = x_606;
x_572 = x_627;
x_573 = x_608;
x_574 = x_609;
x_575 = x_610;
goto block_599;
}
}
block_681:
{
lean_object* x_638; 
x_638 = lean_box(0);
if (lean_obj_tag(x_635) == 0)
{
uint8_t x_639; 
lean_dec(x_631);
x_639 = lean_unbox(x_638);
x_311 = x_639;
x_312 = x_630;
x_313 = x_637;
x_314 = x_633;
x_315 = x_636;
x_316 = x_629;
x_317 = x_634;
x_318 = x_632;
goto block_337;
}
else
{
if (lean_obj_tag(x_631) == 0)
{
uint8_t x_640; 
lean_dec(x_635);
x_640 = lean_unbox(x_638);
x_311 = x_640;
x_312 = x_630;
x_313 = x_637;
x_314 = x_633;
x_315 = x_636;
x_316 = x_629;
x_317 = x_634;
x_318 = x_632;
goto block_337;
}
else
{
if (x_192 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_631);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_641 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_642 = l_Lean_stringToMessageData(x_641);
lean_dec(x_641);
x_643 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_642, x_629, x_634, x_632);
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_13);
return x_643;
}
else
{
lean_object* x_644; uint8_t x_645; 
x_644 = lean_ctor_get(x_635, 0);
lean_inc(x_644);
lean_dec(x_635);
x_645 = !lean_is_exclusive(x_631);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; uint8_t x_648; 
x_646 = lean_ctor_get(x_631, 0);
x_647 = l_Lean_Syntax_getArg(x_13, x_12);
x_648 = l_Lean_Syntax_isNone(x_647);
if (x_648 == 0)
{
uint8_t x_649; 
lean_inc(x_647);
x_649 = l_Lean_Syntax_matchesNull(x_647, x_194);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_647);
lean_free_object(x_631);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_633);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_650 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_651 = l_Lean_stringToMessageData(x_650);
lean_dec(x_650);
x_652 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_651, x_629, x_634, x_632);
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_13);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; 
x_653 = l_Lean_Syntax_getArg(x_647, x_12);
lean_dec(x_647);
x_654 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_655 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_654);
lean_inc(x_653);
x_656 = l_Lean_Syntax_isOfKind(x_653, x_655);
lean_dec(x_655);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
lean_dec(x_653);
lean_free_object(x_631);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_633);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_657 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_658 = l_Lean_stringToMessageData(x_657);
lean_dec(x_657);
x_659 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_658, x_629, x_634, x_632);
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_13);
return x_659;
}
else
{
uint8_t x_660; 
lean_ctor_set(x_631, 0, x_653);
x_660 = lean_unbox(x_638);
x_600 = x_660;
x_601 = x_646;
x_602 = x_630;
x_603 = x_637;
x_604 = x_644;
x_605 = x_633;
x_606 = x_636;
x_607 = x_631;
x_608 = x_629;
x_609 = x_634;
x_610 = x_632;
goto block_628;
}
}
}
else
{
lean_object* x_661; uint8_t x_662; 
lean_dec(x_647);
lean_free_object(x_631);
x_661 = lean_box(0);
x_662 = lean_unbox(x_638);
x_600 = x_662;
x_601 = x_646;
x_602 = x_630;
x_603 = x_637;
x_604 = x_644;
x_605 = x_633;
x_606 = x_636;
x_607 = x_661;
x_608 = x_629;
x_609 = x_634;
x_610 = x_632;
goto block_628;
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_663 = lean_ctor_get(x_631, 0);
lean_inc(x_663);
lean_dec(x_631);
x_664 = l_Lean_Syntax_getArg(x_13, x_12);
x_665 = l_Lean_Syntax_isNone(x_664);
if (x_665 == 0)
{
uint8_t x_666; 
lean_inc(x_664);
x_666 = l_Lean_Syntax_matchesNull(x_664, x_194);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_644);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_633);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_667 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_668 = l_Lean_stringToMessageData(x_667);
lean_dec(x_667);
x_669 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_668, x_629, x_634, x_632);
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_13);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_670 = l_Lean_Syntax_getArg(x_664, x_12);
lean_dec(x_664);
x_671 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_672 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_671);
lean_inc(x_670);
x_673 = l_Lean_Syntax_isOfKind(x_670, x_672);
lean_dec(x_672);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_670);
lean_dec(x_663);
lean_dec(x_644);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_633);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_674 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
x_675 = l_Lean_stringToMessageData(x_674);
lean_dec(x_674);
x_676 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_13, x_675, x_629, x_634, x_632);
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_13);
return x_676;
}
else
{
lean_object* x_677; uint8_t x_678; 
x_677 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_677, 0, x_670);
x_678 = lean_unbox(x_638);
x_600 = x_678;
x_601 = x_663;
x_602 = x_630;
x_603 = x_637;
x_604 = x_644;
x_605 = x_633;
x_606 = x_636;
x_607 = x_677;
x_608 = x_629;
x_609 = x_634;
x_610 = x_632;
goto block_628;
}
}
}
else
{
lean_object* x_679; uint8_t x_680; 
lean_dec(x_664);
x_679 = lean_box(0);
x_680 = lean_unbox(x_638);
x_600 = x_680;
x_601 = x_663;
x_602 = x_630;
x_603 = x_637;
x_604 = x_644;
x_605 = x_633;
x_606 = x_636;
x_607 = x_679;
x_608 = x_629;
x_609 = x_634;
x_610 = x_632;
goto block_628;
}
}
}
}
}
}
block_696:
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_687 = lean_unsigned_to_nat(3u);
x_688 = l_Lean_Syntax_getArg(x_1, x_687);
x_689 = lean_mk_string_unchecked("Term", 4, 4);
x_690 = l_Lean_Syntax_getArg(x_195, x_12);
lean_dec(x_195);
x_691 = l_Lean_Syntax_isToken(x_8, x_690);
lean_dec(x_690);
lean_dec(x_8);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_mk_string_unchecked("builtin_init", 12, 12);
x_693 = l_Lean_Name_mkStr1(x_692);
x_629 = x_684;
x_630 = x_687;
x_631 = x_683;
x_632 = x_686;
x_633 = x_689;
x_634 = x_685;
x_635 = x_682;
x_636 = x_688;
x_637 = x_693;
goto block_681;
}
else
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_mk_string_unchecked("init", 4, 4);
x_695 = l_Lean_Name_mkStr1(x_694);
x_629 = x_684;
x_630 = x_687;
x_631 = x_683;
x_632 = x_686;
x_633 = x_689;
x_634 = x_685;
x_635 = x_682;
x_636 = x_688;
x_637 = x_695;
goto block_681;
}
}
}
block_253:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_218 = l_Lean_Syntax_getArg(x_207, x_12);
x_219 = l_Lean_Syntax_getArg(x_207, x_194);
lean_inc(x_215);
lean_inc(x_214);
x_220 = l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0(x_214, x_218, x_219, x_215, x_216, x_217);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Elab_Command_getRef(x_215, x_216, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Elab_Command_getCurrMacroScope(x_215, x_216, x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lean_Elab_Command_getMainModule___redArg(x_216, x_227);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_228, 0);
x_231 = lean_ctor_get(x_228, 1);
x_232 = l_Lean_SourceInfo_fromRef(x_223, x_206);
lean_dec(x_223);
lean_inc(x_212);
lean_inc(x_200);
lean_inc(x_232);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_200);
lean_ctor_set(x_233, 2, x_212);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_234; 
lean_free_object(x_228);
x_234 = l_Array_empty(lean_box(0));
x_116 = x_199;
x_117 = x_200;
x_118 = x_232;
x_119 = x_201;
x_120 = x_202;
x_121 = x_233;
x_122 = x_214;
x_123 = x_215;
x_124 = x_203;
x_125 = x_230;
x_126 = x_204;
x_127 = x_205;
x_128 = x_226;
x_129 = x_231;
x_130 = x_207;
x_131 = x_209;
x_132 = x_210;
x_133 = x_216;
x_134 = x_213;
x_135 = x_212;
x_136 = x_211;
x_137 = x_234;
goto block_191;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_235 = lean_ctor_get(x_208, 0);
lean_inc(x_235);
lean_dec(x_208);
x_236 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_236);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_237 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_236);
x_238 = l_Lean_SourceInfo_fromRef(x_235, x_198);
lean_dec(x_235);
lean_ctor_set_tag(x_228, 2);
lean_ctor_set(x_228, 1, x_236);
lean_ctor_set(x_228, 0, x_238);
lean_inc(x_232);
x_239 = l_Lean_Syntax_node1(x_232, x_237, x_228);
x_240 = l_Array_mkArray1___redArg(x_239);
x_116 = x_199;
x_117 = x_200;
x_118 = x_232;
x_119 = x_201;
x_120 = x_202;
x_121 = x_233;
x_122 = x_214;
x_123 = x_215;
x_124 = x_203;
x_125 = x_230;
x_126 = x_204;
x_127 = x_205;
x_128 = x_226;
x_129 = x_231;
x_130 = x_207;
x_131 = x_209;
x_132 = x_210;
x_133 = x_216;
x_134 = x_213;
x_135 = x_212;
x_136 = x_211;
x_137 = x_240;
goto block_191;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_228, 0);
x_242 = lean_ctor_get(x_228, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_228);
x_243 = l_Lean_SourceInfo_fromRef(x_223, x_206);
lean_dec(x_223);
lean_inc(x_212);
lean_inc(x_200);
lean_inc(x_243);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_200);
lean_ctor_set(x_244, 2, x_212);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_245; 
x_245 = l_Array_empty(lean_box(0));
x_116 = x_199;
x_117 = x_200;
x_118 = x_243;
x_119 = x_201;
x_120 = x_202;
x_121 = x_244;
x_122 = x_214;
x_123 = x_215;
x_124 = x_203;
x_125 = x_241;
x_126 = x_204;
x_127 = x_205;
x_128 = x_226;
x_129 = x_242;
x_130 = x_207;
x_131 = x_209;
x_132 = x_210;
x_133 = x_216;
x_134 = x_213;
x_135 = x_212;
x_136 = x_211;
x_137 = x_245;
goto block_191;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_208, 0);
lean_inc(x_246);
lean_dec(x_208);
x_247 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_247);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_248 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_247);
x_249 = l_Lean_SourceInfo_fromRef(x_246, x_198);
lean_dec(x_246);
x_250 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_247);
lean_inc(x_243);
x_251 = l_Lean_Syntax_node1(x_243, x_248, x_250);
x_252 = l_Array_mkArray1___redArg(x_251);
x_116 = x_199;
x_117 = x_200;
x_118 = x_243;
x_119 = x_201;
x_120 = x_202;
x_121 = x_244;
x_122 = x_214;
x_123 = x_215;
x_124 = x_203;
x_125 = x_241;
x_126 = x_204;
x_127 = x_205;
x_128 = x_226;
x_129 = x_242;
x_130 = x_207;
x_131 = x_209;
x_132 = x_210;
x_133 = x_216;
x_134 = x_213;
x_135 = x_212;
x_136 = x_211;
x_137 = x_252;
goto block_191;
}
}
}
}
block_115:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_24);
x_30 = l_Array_append(lean_box(0), x_24, x_29);
lean_dec(x_29);
lean_inc(x_16);
lean_inc(x_25);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_27);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_32);
x_34 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_25);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_27);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_36);
x_38 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_27);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_38);
lean_inc(x_16);
lean_inc(x_25);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_24);
lean_inc(x_40);
lean_inc(x_25);
x_41 = l_Lean_Syntax_node1(x_25, x_39, x_40);
x_42 = lean_mk_string_unchecked("Attr", 4, 4);
x_43 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Name_mkStr4(x_5, x_6, x_42, x_43);
x_45 = l_Lean_mkIdentFrom(x_1, x_20, x_22);
lean_dec(x_1);
lean_inc(x_40);
lean_inc(x_25);
x_46 = l_Lean_Syntax_node2(x_25, x_44, x_45, x_40);
lean_inc(x_25);
x_47 = l_Lean_Syntax_node2(x_25, x_37, x_41, x_46);
lean_inc(x_16);
lean_inc(x_25);
x_48 = l_Lean_Syntax_node1(x_25, x_16, x_47);
x_49 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_25);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_25);
x_51 = l_Lean_Syntax_node3(x_25, x_33, x_35, x_48, x_50);
lean_inc(x_16);
lean_inc(x_25);
x_52 = l_Lean_Syntax_node1(x_25, x_16, x_51);
lean_inc_n(x_40, 4);
lean_inc(x_25);
x_53 = l_Lean_Syntax_node6(x_25, x_15, x_31, x_52, x_40, x_40, x_40, x_40);
x_54 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_54);
x_56 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_25);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_25);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_58);
x_60 = lean_mk_string_unchecked("initFn", 6, 6);
lean_inc(x_60);
x_61 = l_String_toSubstring_x27(x_60);
x_62 = l_Lean_Name_mkStr1(x_60);
lean_inc(x_19);
lean_inc(x_21);
x_63 = l_Lean_addMacroScope(x_21, x_62, x_19);
x_64 = lean_box(0);
lean_inc(x_25);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_25);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_inc(x_40);
lean_inc(x_25);
x_66 = l_Lean_Syntax_node2(x_25, x_59, x_65, x_40);
x_67 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_68 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_67);
x_69 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_27);
lean_inc(x_6);
lean_inc(x_5);
x_70 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_69);
x_71 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_25);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_25);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_27);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_73);
x_75 = lean_mk_string_unchecked("IO", 2, 2);
lean_inc(x_75);
x_76 = l_String_toSubstring_x27(x_75);
x_77 = l_Lean_Name_mkStr1(x_75);
lean_inc(x_19);
lean_inc(x_77);
lean_inc(x_21);
x_78 = l_Lean_addMacroScope(x_21, x_77, x_19);
x_79 = lean_box(0);
lean_inc(x_77);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_77);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_64);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_25);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_25);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_83);
x_85 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_85);
x_86 = l_String_toSubstring_x27(x_85);
x_87 = l_Lean_Name_mkStr1(x_85);
lean_inc(x_87);
x_88 = l_Lean_addMacroScope(x_21, x_87, x_19);
lean_inc(x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_79);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_64);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_25);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_25);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_92);
lean_inc(x_16);
lean_inc(x_25);
x_94 = l_Lean_Syntax_node1(x_25, x_16, x_93);
lean_inc(x_25);
x_95 = l_Lean_Syntax_node2(x_25, x_74, x_84, x_94);
lean_inc(x_25);
x_96 = l_Lean_Syntax_node2(x_25, x_70, x_72, x_95);
lean_inc(x_25);
x_97 = l_Lean_Syntax_node1(x_25, x_16, x_96);
lean_inc(x_40);
lean_inc(x_25);
x_98 = l_Lean_Syntax_node2(x_25, x_68, x_40, x_97);
x_99 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_99);
x_101 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_25);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_25);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_103);
lean_inc(x_6);
lean_inc(x_5);
x_104 = l_Lean_Name_mkStr4(x_5, x_6, x_27, x_103);
lean_inc(x_25);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_25);
lean_ctor_set(x_105, 1, x_103);
lean_inc(x_25);
x_106 = l_Lean_Syntax_node2(x_25, x_104, x_105, x_28);
x_107 = lean_mk_string_unchecked("Termination", 11, 11);
x_108 = lean_mk_string_unchecked("suffix", 6, 6);
x_109 = l_Lean_Name_mkStr4(x_5, x_6, x_107, x_108);
lean_inc_n(x_40, 2);
lean_inc(x_25);
x_110 = l_Lean_Syntax_node2(x_25, x_109, x_40, x_40);
lean_inc(x_40);
lean_inc(x_25);
x_111 = l_Lean_Syntax_node4(x_25, x_100, x_102, x_106, x_110, x_40);
lean_inc(x_25);
x_112 = l_Lean_Syntax_node5(x_25, x_55, x_57, x_66, x_98, x_111, x_40);
x_113 = l_Lean_Syntax_node2(x_25, x_17, x_53, x_112);
x_114 = l_Lean_Elab_Command_elabCommand(x_113, x_26, x_23, x_18);
return x_114;
}
block_191:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_138 = l_Array_append(lean_box(0), x_135, x_137);
lean_dec(x_137);
lean_inc(x_117);
lean_inc(x_118);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_118);
lean_ctor_set(x_139, 1, x_117);
lean_ctor_set(x_139, 2, x_138);
lean_inc_n(x_121, 5);
lean_inc(x_118);
x_140 = l_Lean_Syntax_node6(x_118, x_15, x_121, x_121, x_121, x_121, x_139, x_121);
x_141 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_142 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_141);
x_143 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_118);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_118);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_128);
lean_inc(x_125);
x_145 = l_Lean_addMacroScope(x_125, x_126, x_128);
lean_inc(x_136);
lean_inc(x_118);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_118);
lean_ctor_set(x_146, 1, x_119);
lean_ctor_set(x_146, 2, x_145);
lean_ctor_set(x_146, 3, x_136);
lean_inc(x_121);
lean_inc(x_118);
x_147 = l_Lean_Syntax_node2(x_118, x_120, x_146, x_121);
x_148 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_149 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_148);
lean_inc(x_118);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_118);
lean_ctor_set(x_150, 1, x_127);
x_151 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_131);
lean_inc(x_6);
lean_inc(x_5);
x_152 = l_Lean_Name_mkStr4(x_5, x_6, x_131, x_151);
x_153 = lean_mk_string_unchecked("IO", 2, 2);
lean_inc(x_153);
x_154 = l_String_toSubstring_x27(x_153);
x_155 = l_Lean_Name_mkStr1(x_153);
lean_inc(x_155);
x_156 = l_Lean_addMacroScope(x_125, x_155, x_128);
x_157 = lean_box(0);
lean_inc(x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_155);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_136);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_118);
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_118);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_156);
lean_ctor_set(x_162, 3, x_161);
lean_inc(x_117);
lean_inc(x_118);
x_163 = l_Lean_Syntax_node1(x_118, x_117, x_116);
lean_inc(x_118);
x_164 = l_Lean_Syntax_node2(x_118, x_152, x_162, x_163);
lean_inc(x_118);
x_165 = l_Lean_Syntax_node2(x_118, x_124, x_150, x_164);
lean_inc(x_117);
lean_inc(x_118);
x_166 = l_Lean_Syntax_node1(x_118, x_117, x_165);
lean_inc(x_121);
lean_inc(x_118);
x_167 = l_Lean_Syntax_node2(x_118, x_149, x_121, x_166);
x_168 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_168);
x_170 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_118);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_118);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_mk_string_unchecked("withDeclName", 12, 12);
lean_inc(x_131);
lean_inc(x_6);
lean_inc(x_5);
x_173 = l_Lean_Name_mkStr4(x_5, x_6, x_131, x_172);
x_174 = lean_mk_string_unchecked("with_decl_name%", 15, 15);
lean_inc(x_118);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_118);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_syntax_ident(x_122);
x_177 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_177);
lean_inc(x_6);
lean_inc(x_5);
x_178 = l_Lean_Name_mkStr4(x_5, x_6, x_131, x_177);
lean_inc(x_118);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_118);
lean_ctor_set(x_179, 1, x_177);
lean_inc(x_118);
x_180 = l_Lean_Syntax_node2(x_118, x_178, x_179, x_134);
lean_inc(x_121);
lean_inc(x_118);
x_181 = l_Lean_Syntax_node4(x_118, x_173, x_175, x_121, x_176, x_180);
x_182 = lean_mk_string_unchecked("Termination", 11, 11);
x_183 = lean_mk_string_unchecked("suffix", 6, 6);
x_184 = l_Lean_Name_mkStr4(x_5, x_6, x_182, x_183);
lean_inc_n(x_121, 2);
lean_inc(x_118);
x_185 = l_Lean_Syntax_node2(x_118, x_184, x_121, x_121);
lean_inc(x_121);
lean_inc(x_118);
x_186 = l_Lean_Syntax_node4(x_118, x_169, x_171, x_181, x_185, x_121);
lean_inc(x_118);
x_187 = l_Lean_Syntax_node5(x_118, x_142, x_144, x_147, x_167, x_186, x_121);
lean_inc(x_118);
x_188 = l_Lean_Syntax_node2(x_118, x_132, x_140, x_187);
x_189 = l_Lean_Syntax_node2(x_118, x_117, x_188, x_130);
x_190 = l_Lean_Elab_Command_elabCommand(x_189, x_123, x_133, x_129);
return x_190;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange_x3f___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDeclarationRanges___at___Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addDeclarationRangesFromSyntax___at___Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addDeclarationRangesForBuiltin___at___Lean_Elab_Command_elabInitialize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("initialize", 10, 10);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabInitialize", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitialize), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7438_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("axiom", 5, 5);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = lean_mk_string_unchecked("Declaration", 11, 11);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(7438u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_5);
x_25 = l_Lean_registerTraceClass(x_4, x_24, x_23, x_1);
return x_25;
}
}
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualInductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Declaration(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualInductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_7438_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
