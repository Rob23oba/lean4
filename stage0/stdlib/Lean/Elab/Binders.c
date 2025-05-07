// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Lean.Elab.Quotation.Precheck Lean.Elab.Term Lean.Elab.BindersUtil Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.TerminationHint
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow_declRange__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall__1(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun__1(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandForall__1(lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun_declRange__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkBinderAnnotations;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_10744_(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2008_(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__1(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_kindOfBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_quoteAutoTactic___lam__0(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(lean_object*, uint8_t, size_t, size_t, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_kindOfBinderName___boxed(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandForall_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
lean_object* l_Lean_Elab_Term_universeConstraintsCheckpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Syntax_getNumArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_mkHole(x_1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Environment_mainModule(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 10);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_addMacroScope(x_9, x_1, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Environment_mainModule(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 10);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_addMacroScope(x_15, x_1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("x", 1, 1);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Core_withFreshMacroScope___redArg(x_6, x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg(x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkIdentFrom(x_1, x_12, x_2);
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
x_16 = l_Lean_mkIdentFrom(x_1, x_14, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("hole", 4, 4);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isNone(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_mk_string_unchecked("inst", 4, 4);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Core_withFreshMacroScope___redArg(x_11, x_2, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_mkIdentFrom(x_1, x_14, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_mkIdentFrom(x_1, x_18, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_1, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_kindOfBinderName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_isImplementationDetail(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_kindOfBinderName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_kindOfBinderName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Syntax", 6, 6);
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_35; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = l_Lean_Name_mkStr2(x_16, x_17);
x_23 = lean_mk_string_unchecked("Array", 5, 5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
x_25 = l_Lean_Expr_const___override(x_22, x_21);
x_26 = lean_array_uget(x_2, x_4);
x_44 = lean_mk_string_unchecked("null", 4, 4);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = lean_name_eq(x_1, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
x_35 = x_46;
goto block_43;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_Syntax_isAntiquotSuffixSplice(x_26);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Syntax_isAntiquotSplice(x_26);
x_35 = x_48;
goto block_43;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
goto block_34;
}
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_mk_string_unchecked("invalid auto tactic, antiquotation is not allowed", 49, 49);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_throwErrorAt___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__1___redArg(x_26, x_28, x_6, x_7, x_8);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_43:
{
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Elab_Term_quoteAutoTactic(x_26, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_string_unchecked("push", 4, 4);
x_40 = l_Lean_Name_mkStr2(x_23, x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_24);
x_42 = l_Lean_mkApp3(x_41, x_25, x_5, x_37);
x_9 = x_42;
x_10 = x_38;
goto block_15;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
return x_36;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
goto block_34;
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_mkStrLit(x_4);
lean_inc(x_2);
x_7 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_1, x_2, x_5);
x_8 = l_Lean_mkAppB(x_2, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_3);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Syntax", 6, 6);
x_14 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_15 = lean_mk_string_unchecked("namespace", 9, 9);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_const___override(x_16, x_17);
x_19 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_11);
x_20 = l_Lean_Expr_app___override(x_18, x_19);
x_7 = x_20;
goto block_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Syntax", 6, 6);
x_25 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_26 = lean_mk_string_unchecked("decl", 4, 4);
x_27 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Expr_const___override(x_27, x_28);
x_30 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_21);
x_31 = lean_mk_string_unchecked("String", 6, 6);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Lean_Expr_const___override(x_32, x_28);
x_34 = lean_mk_string_unchecked("List", 4, 4);
x_35 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_34);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_box(0);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_37);
lean_inc(x_3);
x_38 = l_Lean_Expr_const___override(x_36, x_3);
lean_inc(x_33);
x_39 = l_Lean_Expr_app___override(x_38, x_33);
x_40 = lean_mk_string_unchecked("cons", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_34, x_40);
x_42 = l_Lean_Expr_const___override(x_41, x_3);
x_43 = l_Lean_Expr_app___override(x_42, x_33);
x_44 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_39, x_43, x_22);
lean_dec(x_39);
x_45 = l_Lean_mkAppB(x_29, x_30, x_44);
x_7 = x_45;
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_1, x_2, x_6);
x_9 = l_Lean_mkAppB(x_2, x_7, x_8);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("Syntax", 6, 6);
x_55 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_56 = lean_mk_string_unchecked("namespace", 9, 9);
x_57 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
x_58 = lean_box(0);
x_59 = l_Lean_Expr_const___override(x_57, x_58);
x_60 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_52);
x_61 = l_Lean_Expr_app___override(x_59, x_60);
x_48 = x_61;
goto block_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
lean_dec(x_46);
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Syntax", 6, 6);
x_66 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_67 = lean_mk_string_unchecked("decl", 4, 4);
x_68 = l_Lean_Name_mkStr4(x_64, x_65, x_66, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Expr_const___override(x_68, x_69);
x_71 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_62);
x_72 = lean_mk_string_unchecked("String", 6, 6);
x_73 = l_Lean_Name_mkStr1(x_72);
x_74 = l_Lean_Expr_const___override(x_73, x_69);
x_75 = lean_mk_string_unchecked("List", 4, 4);
x_76 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_75);
x_77 = l_Lean_Name_mkStr2(x_75, x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
lean_inc(x_79);
x_80 = l_Lean_Expr_const___override(x_77, x_79);
lean_inc(x_74);
x_81 = l_Lean_Expr_app___override(x_80, x_74);
x_82 = lean_mk_string_unchecked("cons", 4, 4);
x_83 = l_Lean_Name_mkStr2(x_75, x_82);
x_84 = l_Lean_Expr_const___override(x_83, x_79);
x_85 = l_Lean_Expr_app___override(x_84, x_74);
x_86 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_81, x_85, x_63);
lean_dec(x_81);
x_87 = l_Lean_mkAppB(x_70, x_71, x_86);
x_48 = x_87;
goto block_51;
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
lean_inc(x_2);
x_49 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_1, x_2, x_47);
x_50 = l_Lean_mkAppB(x_2, x_48, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_quoteAutoTactic___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("invalid auto tactic, tactic is missing", 38, 38);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_Lean_Syntax_isAntiquot(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Syntax", 6, 6);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("Array", 5, 5);
x_17 = lean_mk_string_unchecked("empty", 5, 5);
x_18 = l_Lean_Name_mkStr2(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
x_21 = l_Lean_Expr_const___override(x_18, x_20);
x_22 = l_Lean_Expr_app___override(x_21, x_15);
x_23 = lean_array_size(x_9);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(x_8, x_9, x_23, x_25, x_22, x_2, x_3, x_4);
lean_dec(x_9);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_11);
x_30 = l_Lean_Name_mkStr3(x_11, x_12, x_29);
x_31 = l_Lean_Expr_const___override(x_30, x_14);
x_32 = lean_mk_string_unchecked("SourceInfo", 10, 10);
x_33 = lean_mk_string_unchecked("none", 4, 4);
x_34 = l_Lean_Name_mkStr3(x_11, x_32, x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_14);
x_36 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_8);
x_37 = l_Lean_mkApp3(x_31, x_35, x_36, x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_11);
x_41 = l_Lean_Name_mkStr3(x_11, x_12, x_40);
x_42 = l_Lean_Expr_const___override(x_41, x_14);
x_43 = lean_mk_string_unchecked("SourceInfo", 10, 10);
x_44 = lean_mk_string_unchecked("none", 4, 4);
x_45 = l_Lean_Name_mkStr3(x_11, x_43, x_44);
x_46 = l_Lean_Expr_const___override(x_45, x_14);
x_47 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_8);
x_48 = l_Lean_mkApp3(x_42, x_46, x_47, x_38);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
return x_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
x_50 = lean_mk_string_unchecked("invalid auto tactic, antiquotation is not allowed", 49, 49);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = l_Lean_throwErrorAt___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__1___redArg(x_1, x_51, x_2, x_3, x_4);
lean_dec(x_1);
return x_52;
}
}
case 2:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_1, 1);
x_55 = lean_ctor_get(x_1, 0);
lean_dec(x_55);
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("mkAtom", 6, 6);
x_58 = l_Lean_Name_mkStr2(x_56, x_57);
x_59 = lean_box(0);
x_60 = l_Lean_Expr_const___override(x_58, x_59);
x_61 = l_Lean_mkStrLit(x_54);
x_62 = l_Lean_Expr_app___override(x_60, x_61);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("mkAtom", 6, 6);
x_66 = l_Lean_Name_mkStr2(x_64, x_65);
x_67 = lean_box(0);
x_68 = l_Lean_Expr_const___override(x_66, x_67);
x_69 = l_Lean_mkStrLit(x_63);
x_70 = l_Lean_Expr_app___override(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 3);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed), 1, 0);
x_75 = lean_mk_string_unchecked("Lean", 4, 4);
x_76 = lean_mk_string_unchecked("Syntax", 6, 6);
x_77 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_76);
lean_inc(x_75);
x_78 = l_Lean_Name_mkStr3(x_75, x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_Expr_const___override(x_78, x_79);
x_81 = lean_mk_string_unchecked("SourceInfo", 10, 10);
x_82 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_75);
x_83 = l_Lean_Name_mkStr3(x_75, x_81, x_82);
x_84 = l_Lean_Expr_const___override(x_83, x_79);
x_85 = lean_mk_string_unchecked("String", 6, 6);
x_86 = lean_mk_string_unchecked("toSubstring", 11, 11);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = l_Lean_Expr_const___override(x_87, x_79);
x_89 = lean_box(1);
x_90 = lean_unbox(x_89);
lean_inc(x_72);
x_91 = l_Lean_Name_toString(x_72, x_90, x_74);
x_92 = l_Lean_mkStrLit(x_91);
x_93 = l_Lean_Expr_app___override(x_88, x_92);
x_94 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_72);
x_95 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_96 = l_Lean_Name_mkStr3(x_75, x_76, x_95);
x_97 = l_Lean_Expr_const___override(x_96, x_79);
x_98 = lean_mk_string_unchecked("List", 4, 4);
x_99 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_98);
x_100 = l_Lean_Name_mkStr2(x_98, x_99);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_79);
lean_inc(x_102);
x_103 = l_Lean_Expr_const___override(x_100, x_102);
lean_inc(x_97);
x_104 = l_Lean_Expr_app___override(x_103, x_97);
x_105 = lean_mk_string_unchecked("cons", 4, 4);
x_106 = l_Lean_Name_mkStr2(x_98, x_105);
x_107 = l_Lean_Expr_const___override(x_106, x_102);
x_108 = l_Lean_Expr_app___override(x_107, x_97);
x_109 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_104, x_108, x_73);
lean_dec(x_104);
x_110 = l_Lean_mkApp4(x_80, x_84, x_93, x_94, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_4);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_quoteAutoTactic___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_38; lean_object* x_39; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_78; lean_object* x_79; 
x_63 = lean_st_ref_get(x_6, x_7);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
lean_dec(x_64);
x_79 = l_Lean_Environment_asyncPrefix_x3f(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_box(0);
x_66 = x_80;
goto block_77;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_66 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_st_ref_get(x_6, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("_auto", 5, 5);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = l_Lean_Name_append(x_66, x_71);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Environment_mainModule(x_73);
lean_dec(x_73);
x_75 = lean_ctor_get(x_5, 10);
lean_inc(x_75);
x_76 = l_Lean_addMacroScope(x_74, x_72, x_75);
x_38 = x_76;
x_39 = x_69;
goto block_62;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
lean_dec(x_4);
x_38 = x_82;
x_39 = x_7;
goto block_62;
}
block_37:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_box(0);
lean_inc(x_8);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
x_14 = lean_box(0);
x_15 = lean_box(1);
lean_inc(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_20 = l_Lean_addDecl(x_19, x_5, x_6, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_compileDecl(x_19, x_23, x_5, x_6, x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_62:
{
lean_object* x_40; 
x_40 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_string_unchecked("Elab", 4, 4);
x_44 = lean_mk_string_unchecked("autoParam", 9, 9);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
lean_inc(x_45);
x_46 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_45, x_5, x_42);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Syntax", 6, 6);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = lean_box(0);
x_53 = l_Lean_Expr_const___override(x_51, x_52);
x_54 = lean_unbox(x_47);
lean_dec(x_47);
if (x_54 == 0)
{
lean_dec(x_45);
x_8 = x_38;
x_9 = x_41;
x_10 = x_53;
x_11 = x_48;
goto block_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_41);
x_55 = l_Lean_MessageData_ofExpr(x_41);
x_56 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_45, x_55, x_2, x_3, x_5, x_6, x_48);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_8 = x_38;
x_9 = x_41;
x_10 = x_53;
x_11 = x_57;
goto block_37;
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed), 7, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_2);
x_9 = l_Lean_Core_withFreshMacroScope___redArg(x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_declareTacticSyntax___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_declareTacticSyntax___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_declareTacticSyntax(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_isNone(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_2, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("binderDefault", 13, 13);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_name_eq(x_11, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_mk_string_unchecked("binderTactic", 12, 12);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_19 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_18);
x_20 = lean_name_eq(x_11, x_19);
lean_dec(x_19);
lean_dec(x_11);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_dec(x_10);
x_24 = lean_box(0);
lean_inc(x_6);
lean_inc(x_23);
x_25 = l_Lean_Elab_Term_declareTacticSyntax___redArg(x_23, x_24, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_5, 5);
lean_inc(x_31);
x_32 = l_Lean_SourceInfo_fromRef(x_31, x_17);
lean_dec(x_31);
x_33 = lean_ctor_get(x_5, 10);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Environment_mainModule(x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("app", 3, 3);
x_37 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_36);
x_38 = lean_mk_string_unchecked("autoParam", 9, 9);
lean_inc(x_38);
x_39 = l_String_toSubstring_x27(x_38);
x_40 = l_Lean_Name_mkStr1(x_38);
lean_inc(x_40);
x_41 = l_Lean_addMacroScope(x_35, x_40, x_33);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_32);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_mk_string_unchecked("null", 4, 4);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = l_Lean_mkIdentFrom(x_23, x_26, x_17);
lean_dec(x_23);
lean_inc(x_32);
x_50 = l_Lean_Syntax_node2(x_32, x_48, x_1, x_49);
x_51 = l_Lean_Syntax_node2(x_32, x_37, x_46, x_50);
lean_ctor_set(x_28, 0, x_51);
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_ctor_get(x_5, 5);
lean_inc(x_54);
x_55 = l_Lean_SourceInfo_fromRef(x_54, x_17);
lean_dec(x_54);
x_56 = lean_ctor_get(x_5, 10);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = l_Lean_Environment_mainModule(x_57);
lean_dec(x_57);
x_59 = lean_mk_string_unchecked("app", 3, 3);
x_60 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_59);
x_61 = lean_mk_string_unchecked("autoParam", 9, 9);
lean_inc(x_61);
x_62 = l_String_toSubstring_x27(x_61);
x_63 = l_Lean_Name_mkStr1(x_61);
lean_inc(x_63);
x_64 = l_Lean_addMacroScope(x_58, x_63, x_56);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_55);
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_mk_string_unchecked("null", 4, 4);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = l_Lean_mkIdentFrom(x_23, x_26, x_17);
lean_dec(x_23);
lean_inc(x_55);
x_73 = l_Lean_Syntax_node2(x_55, x_71, x_1, x_72);
x_74 = l_Lean_Syntax_node2(x_55, x_60, x_69, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_53);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_25);
if (x_76 == 0)
{
return x_25;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_25, 0);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_25);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_st_ref_get(x_6, x_7);
lean_dec(x_6);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_ctor_get(x_5, 5);
lean_inc(x_84);
x_85 = l_Lean_Syntax_getArg(x_10, x_83);
lean_dec(x_10);
x_86 = l_Lean_SourceInfo_fromRef(x_84, x_8);
lean_dec(x_84);
x_87 = lean_ctor_get(x_5, 10);
lean_inc(x_87);
lean_dec(x_5);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Environment_mainModule(x_88);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("app", 3, 3);
x_91 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_90);
x_92 = lean_mk_string_unchecked("optParam", 8, 8);
lean_inc(x_92);
x_93 = l_String_toSubstring_x27(x_92);
x_94 = l_Lean_Name_mkStr1(x_92);
lean_inc(x_94);
x_95 = l_Lean_addMacroScope(x_89, x_94, x_87);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_86);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_86);
lean_ctor_set(x_100, 1, x_93);
lean_ctor_set(x_100, 2, x_95);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_mk_string_unchecked("null", 4, 4);
x_102 = l_Lean_Name_mkStr1(x_101);
lean_inc(x_86);
x_103 = l_Lean_Syntax_node2(x_86, x_102, x_1, x_85);
x_104 = l_Lean_Syntax_node2(x_86, x_91, x_100, x_103);
lean_ctor_set(x_80, 0, x_104);
return x_80;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_105 = lean_ctor_get(x_80, 0);
x_106 = lean_ctor_get(x_80, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_80);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_ctor_get(x_5, 5);
lean_inc(x_108);
x_109 = l_Lean_Syntax_getArg(x_10, x_107);
lean_dec(x_10);
x_110 = l_Lean_SourceInfo_fromRef(x_108, x_8);
lean_dec(x_108);
x_111 = lean_ctor_get(x_5, 10);
lean_inc(x_111);
lean_dec(x_5);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
lean_dec(x_105);
x_113 = l_Lean_Environment_mainModule(x_112);
lean_dec(x_112);
x_114 = lean_mk_string_unchecked("app", 3, 3);
x_115 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_114);
x_116 = lean_mk_string_unchecked("optParam", 8, 8);
lean_inc(x_116);
x_117 = l_String_toSubstring_x27(x_116);
x_118 = l_Lean_Name_mkStr1(x_116);
lean_inc(x_118);
x_119 = l_Lean_addMacroScope(x_113, x_118, x_111);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_inc(x_110);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_117);
lean_ctor_set(x_124, 2, x_119);
lean_ctor_set(x_124, 3, x_123);
x_125 = lean_mk_string_unchecked("null", 4, 4);
x_126 = l_Lean_Name_mkStr1(x_125);
lean_inc(x_110);
x_127 = l_Lean_Syntax_node2(x_110, x_126, x_1, x_109);
x_128 = l_Lean_Syntax_node2(x_110, x_115, x_124, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_106);
return x_129;
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_7);
return x_130;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_24; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_13);
x_33 = l_Lean_Syntax_getKind(x_13);
x_34 = lean_mk_string_unchecked("ident", 5, 5);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Parser", 6, 6);
x_39 = lean_mk_string_unchecked("Term", 4, 4);
x_40 = lean_mk_string_unchecked("hole", 4, 4);
x_41 = l_Lean_Name_mkStr4(x_37, x_38, x_39, x_40);
x_42 = lean_name_eq(x_33, x_41);
lean_dec(x_41);
lean_dec(x_33);
x_24 = x_42;
goto block_32;
}
else
{
lean_dec(x_33);
x_24 = x_36;
goto block_32;
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
x_10 = x_17;
goto _start;
}
block_32:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
x_25 = lean_mk_string_unchecked("identifier or `_` expected", 26, 26);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_13, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
x_16 = x_13;
x_17 = x_10;
goto block_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_24; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_13);
x_33 = l_Lean_Syntax_getKind(x_13);
x_34 = lean_mk_string_unchecked("ident", 5, 5);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Parser", 6, 6);
x_39 = lean_mk_string_unchecked("Term", 4, 4);
x_40 = lean_mk_string_unchecked("hole", 4, 4);
x_41 = l_Lean_Name_mkStr4(x_37, x_38, x_39, x_40);
x_42 = lean_name_eq(x_33, x_41);
lean_dec(x_41);
lean_dec(x_33);
x_24 = x_42;
goto block_32;
}
else
{
lean_dec(x_33);
x_24 = x_36;
goto block_32;
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_16);
x_22 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(x_1, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_22;
}
block_32:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
x_25 = lean_mk_string_unchecked("identifier or `_` expected", 26, 26);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_13, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
x_16 = x_13;
x_17 = x_10;
goto block_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(x_10, x_12, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_10);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_getArg(x_1, x_18);
x_21 = lean_array_uset(x_4, x_3, x_19);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_14, x_20);
lean_dec(x_20);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_array_uset(x_21, x_3, x_24);
x_3 = x_28;
x_4 = x_29;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_10);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_getArg(x_1, x_18);
x_21 = lean_array_uset(x_4, x_3, x_19);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_14, x_20);
lean_dec(x_20);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_array_uset(x_21, x_3, x_24);
x_3 = x_28;
x_4 = x_29;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_10);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Syntax_getArg(x_1, x_18);
x_21 = l_Lean_Syntax_getArg(x_1, x_19);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_14, x_20);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_22, x_21, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_array_uset(x_4, x_3, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_24);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_add(x_3, x_32);
x_34 = lean_array_uset(x_27, x_3, x_29);
x_3 = x_33;
x_4 = x_34;
x_11 = x_25;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
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
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_121; 
lean_inc(x_1);
x_9 = l_Lean_Syntax_getKind(x_1);
x_121 = l_Lean_Syntax_isIdent(x_1);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_mk_string_unchecked("Lean", 4, 4);
x_123 = lean_mk_string_unchecked("Parser", 6, 6);
x_124 = lean_mk_string_unchecked("Term", 4, 4);
x_125 = lean_mk_string_unchecked("hole", 4, 4);
x_126 = l_Lean_Name_mkStr4(x_122, x_123, x_124, x_125);
x_127 = lean_name_eq(x_9, x_126);
lean_dec(x_126);
x_10 = x_127;
goto block_120;
}
else
{
x_10 = x_121;
goto block_120;
}
block_120:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_name_eq(x_9, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_mk_string_unchecked("implicitBinder", 14, 14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_18 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_17);
x_19 = lean_name_eq(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
x_22 = lean_name_eq(x_9, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("instBinder", 10, 10);
x_24 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_23);
x_25 = lean_name_eq(x_9, x_24);
lean_dec(x_24);
lean_dec(x_9);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_28, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
lean_dec(x_1);
x_34 = lean_box(3);
lean_inc(x_31);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_36);
x_37 = lean_mk_empty_array_with_capacity(x_27);
x_38 = lean_array_push(x_37, x_35);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(2u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_43 = lean_box(3);
lean_inc(x_39);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_45);
x_46 = lean_mk_empty_array_with_capacity(x_27);
x_47 = lean_array_push(x_46, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
lean_inc(x_2);
x_55 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; size_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_size(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_usize_of_nat(x_59);
x_61 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(x_1, x_58, x_60, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_55, 0);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_55);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_66 = lean_unsigned_to_nat(1u);
x_67 = l_Lean_Syntax_getArg(x_1, x_66);
lean_inc(x_2);
x_68 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; size_t x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_array_size(x_69);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_usize_of_nat(x_72);
x_74 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(x_1, x_71, x_73, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_68);
if (x_75 == 0)
{
return x_68;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_68, 0);
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_68);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_79 = lean_unsigned_to_nat(1u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
lean_inc(x_2);
x_81 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; size_t x_84; lean_object* x_85; size_t x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_array_size(x_82);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_usize_of_nat(x_85);
x_87 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(x_1, x_84, x_86, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_2);
lean_dec(x_1);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_9);
lean_inc(x_1);
x_92 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_box(0);
x_96 = lean_unbox(x_95);
x_97 = l_Lean_mkHole(x_1, x_96);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_94);
lean_ctor_set(x_99, 2, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_100);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_mk_empty_array_with_capacity(x_101);
x_103 = lean_array_push(x_102, x_99);
lean_ctor_set(x_92, 0, x_103);
return x_92;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = lean_ctor_get(x_92, 0);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_92);
x_106 = lean_box(0);
x_107 = lean_unbox(x_106);
x_108 = l_Lean_mkHole(x_1, x_107);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_108);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_111);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_mk_empty_array_with_capacity(x_112);
x_114 = lean_array_push(x_113, x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
return x_115;
}
}
else
{
uint8_t x_116; 
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_92);
if (x_116 == 0)
{
return x_92;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_92, 0);
x_118 = lean_ctor_get(x_92, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_92);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_mk_string_unchecked("failed to infer binder type", 27, 27);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(x_1, x_2, x_12, x_4, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("failed to infer universe levels in binder type", 46, 46);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo(x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_2, x_10, x_11, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_Syntax_getId(x_9);
x_11 = lean_erase_macro_scopes(x_10);
x_12 = l_Lean_Name_isAtomic(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_mk_string_unchecked("invalid binder name '", 21, 21);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = l_Lean_MessageData_ofName(x_11);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("', it must be atomic", 20, 20);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2008_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("checkBinderAnnotations", 22, 22);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("check whether type is a class instance whenever the binder annotation `[...]` is used", 85, 85);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("Term", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_2);
x_12 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_3, x_7, x_11, x_1);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_2);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 8);
lean_dec(x_10);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed), 9, 1);
lean_closure_set(x_16, 0, x_14);
x_28 = lean_box(3);
x_29 = lean_unbox(x_28);
x_30 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_15, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_expr_has_loose_bvar(x_14, x_31);
lean_dec(x_14);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
lean_dec(x_12);
x_33 = lean_mk_string_unchecked("invalid parametric local instance, parameter with type", 54, 54);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_indentExpr(x_13);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("\ndoes not have forward dependencies, type class resolution cannot use this kind of local instance because it will not be able to infer a value for this parameter.", 162, 162);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
else
{
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_27;
}
}
else
{
lean_dec(x_14);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_27;
}
block_27:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_12, x_15, x_13, x_16, x_25, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_26;
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_9, 0, x_43);
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Elab_Term_addLocalVarInfo(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_array_push(x_4, x_20);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_5, x_6, x_19, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed), 14, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
x_17 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_kindOfBinderName(x_17);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_20 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_17, x_19, x_6, x_16, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_19 = l_Lean_Elab_Term_elabType(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_58; uint8_t x_82; uint8_t x_83; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_18);
lean_inc(x_20);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_82 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_83 = l_Lean_BinderInfo_isInstImplicit(x_82);
if (x_83 == 0)
{
x_58 = x_83;
goto block_81;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_9, 2);
lean_inc(x_84);
x_85 = l_Lean_Elab_Term_checkBinderAnnotations;
x_86 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_84, x_85);
lean_dec(x_84);
x_58 = x_86;
goto block_81;
}
block_57:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 5);
lean_inc(x_32);
x_33 = l_Lean_replaceRef(x_18, x_32);
lean_dec(x_32);
lean_dec(x_18);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 7);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 8);
lean_inc(x_41);
x_42 = lean_ctor_get(x_29, 9);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 10);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_29, sizeof(void*)*13);
x_45 = lean_ctor_get(x_29, 11);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_29, sizeof(void*)*13 + 1);
x_47 = lean_ctor_get(x_29, 12);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 3, x_37);
lean_ctor_set(x_48, 4, x_38);
lean_ctor_set(x_48, 5, x_33);
lean_ctor_set(x_48, 6, x_39);
lean_ctor_set(x_48, 7, x_40);
lean_ctor_set(x_48, 8, x_41);
lean_ctor_set(x_48, 9, x_42);
lean_ctor_set(x_48, 10, x_43);
lean_ctor_set(x_48, 11, x_45);
lean_ctor_set(x_48, 12, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*13, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*13 + 1, x_46);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_20);
x_49 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(x_20, x_25, x_26, x_27, x_28, x_48, x_30, x_31);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_15, x_3, x_4, x_1, x_2, x_20, x_50, x_25, x_26, x_27, x_28, x_29, x_30, x_51);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
block_81:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_24);
lean_dec(x_18);
x_59 = lean_box(0);
x_60 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_15, x_3, x_4, x_1, x_2, x_20, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_60;
}
else
{
lean_object* x_61; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_61 = l_Lean_Meta_isClass_x3f(x_20, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_mk_string_unchecked("invalid binder annotation, type is not a class instance", 55, 55);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = l_Lean_indentExpr(x_20);
if (lean_is_scalar(x_24)) {
 x_67 = lean_alloc_ctor(7, 2, 0);
} else {
 x_67 = x_24;
 lean_ctor_set_tag(x_67, 7);
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("\nuse the command `set_option checkBinderAnnotations false` to disable the check", 79, 79);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_18, x_70, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_18);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_62);
lean_dec(x_24);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_dec(x_61);
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_76;
goto block_57;
}
}
else
{
uint8_t x_77; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_15);
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
x_77 = !lean_is_exclusive(x_61);
if (x_77 == 0)
{
return x_61;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_61, 0);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_61);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_18);
lean_dec(x_15);
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
x_87 = !lean_is_exclusive(x_19);
if (x_87 == 0)
{
return x_19;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_19, 0);
x_89 = lean_ctor_get(x_19, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_19);
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
lean_dec(x_15);
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
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_1, x_3, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed), 11, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_20);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(x_17, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_apply_8(x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_isEmpty___redArg(x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
x_13 = l_Lean_Elab_Term_universeConstraintsCheckpoint(lean_box(0), x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBindersEx___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_size(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(x_10, x_12, x_2);
x_14 = lean_apply_8(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___redArg___lam__0), 9, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_Elab_Term_elabBindersEx___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinders___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_apply_8(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_1);
x_15 = l_Lean_Elab_Term_elabBinders___redArg(x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinder___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinder___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_32 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_32);
lean_inc(x_2);
x_34 = l_Lean_Syntax_isOfKind(x_2, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Syntax_isIdent(x_2);
x_8 = x_35;
goto block_31;
}
else
{
x_8 = x_34;
goto block_31;
}
block_31:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_mk_string_unchecked("unexpected type ascription", 26, 26);
x_10 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_9, x_3, x_4);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_3, 5);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
x_15 = lean_mk_string_unchecked("explicitBinder", 14, 14);
x_16 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_15);
x_17 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_14);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
lean_inc(x_20);
lean_inc(x_14);
x_21 = l_Lean_Syntax_node1(x_14, x_20, x_2);
x_22 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_14);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_20);
lean_inc(x_14);
x_24 = l_Lean_Syntax_node2(x_14, x_20, x_23, x_1);
x_25 = l_Array_mkArray0(lean_box(0));
lean_inc(x_14);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_14);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Syntax_node5(x_14, x_16, x_18, x_21, x_24, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandSimpleBinderWithType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Syntax_getArg(x_8, x_9);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_12, x_13);
lean_dec(x_12);
x_15 = lean_array_uget(x_4, x_3);
x_16 = l_Lean_Elab_Term_expandSimpleBinderWithType(x_14, x_15, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_4, x_3, x_19);
x_21 = lean_usize_of_nat(x_13);
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_20, x_3, x_17);
x_3 = x_22;
x_4 = x_23;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("forall", 6, 6);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_13, x_16);
lean_dec(x_13);
x_18 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_21 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = l_Lean_Syntax_getArg(x_1, x_11);
x_23 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_24 = lean_array_size(x_23);
x_25 = lean_usize_of_nat(x_16);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(x_1, x_24, x_25, x_23, x_2, x_3);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_2, 5);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
x_34 = l_Lean_SourceInfo_fromRef(x_31, x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = l_Array_mkArray0(lean_box(0));
lean_inc(x_38);
x_39 = l_Array_append(lean_box(0), x_38, x_28);
lean_dec(x_28);
lean_inc(x_37);
lean_inc(x_34);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_34);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_34);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Syntax_node5(x_34, x_8, x_35, x_40, x_41, x_43, x_30);
lean_ctor_set(x_26, 0, x_44);
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = lean_unsigned_to_nat(4u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
lean_dec(x_1);
x_49 = lean_ctor_get(x_2, 5);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_SourceInfo_fromRef(x_49, x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
x_54 = lean_mk_string_unchecked("null", 4, 4);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Array_mkArray0(lean_box(0));
lean_inc(x_56);
x_57 = l_Array_append(lean_box(0), x_56, x_45);
lean_dec(x_45);
lean_inc(x_55);
lean_inc(x_52);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_52);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_52);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Syntax_node5(x_52, x_8, x_53, x_58, x_59, x_61, x_48);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_46);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandForall(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandForall__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("forall", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandForall", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandForall___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandForall_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandForall", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(264u);
x_8 = lean_unsigned_to_nat(41u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(268u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(45u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(57u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_elabType(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_unbox(x_14);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_Meta_mkForallFVars(x_3, x_12, x_16, x_2, x_17, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("forall", 6, 6);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_matchesNull(x_18, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = lean_box(x_19);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_28 = l_Lean_Elab_Term_elabBinders___redArg(x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabForall___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Term_elabForall___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("forall", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabForall", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabForall", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(270u);
x_8 = lean_unsigned_to_nat(30u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(276u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(34u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(44u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("arrow", 5, 5);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("arrow", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("precheckArrow", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckArrow), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("arrow", 5, 5);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_elabType(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
lean_inc(x_7);
x_23 = l_Lean_Elab_Term_elabType(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_7, x_25);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_mk_string_unchecked("a", 1, 1);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Environment_mainModule(x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_6, 10);
lean_inc(x_33);
lean_dec(x_6);
x_34 = l_Lean_addMacroScope(x_32, x_30, x_33);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Expr_forallE___override(x_34, x_19, x_24, x_36);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_mk_string_unchecked("a", 1, 1);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_Environment_mainModule(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_6, 10);
lean_inc(x_44);
lean_dec(x_6);
x_45 = l_Lean_addMacroScope(x_43, x_41, x_44);
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_Expr_forallE___override(x_45, x_19, x_24, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
}
else
{
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabArrow___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("arrow", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabArrow", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabArrow", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(285u);
x_8 = lean_unsigned_to_nat(27u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(292u);
x_11 = lean_unsigned_to_nat(50u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(31u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(40u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(1);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_15);
x_19 = l_Lean_Meta_mkForallFVars(x_2, x_11, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___redArg___lam__0___boxed), 9, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_10);
x_17 = l_Lean_Elab_Term_elabBinders___redArg(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDepArrow___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDepArrow___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabDepArrow___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDepArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("depArrow", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabDepArrow", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabDepArrow", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("The dependent arrow. `(x : α) → β` is equivalent to `∀ x : α, β`, but we usually\nreserve the latter for propositions. Also written as `Π x : α, β` (the \"Pi-type\")\nin the literature. ", 193, 182);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabDepArrow", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(298u);
x_8 = lean_unsigned_to_nat(30u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(303u);
x_11 = lean_unsigned_to_nat(38u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(34u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(46u);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("hole", 4, 4);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
lean_inc(x_17);
x_23 = l_Lean_Syntax_isOfKind(x_17, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_mk_string_unchecked("ident", 5, 5);
x_25 = l_Lean_Name_mkStr1(x_24);
lean_inc(x_17);
x_26 = l_Lean_Syntax_isOfKind(x_17, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_4);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
x_6 = x_17;
x_7 = x_5;
goto block_13;
}
}
else
{
x_6 = x_17;
x_7 = x_5;
goto block_13;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_push(x_4, x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Term", 4, 4);
x_22 = lean_mk_string_unchecked("hole", 4, 4);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
lean_inc(x_18);
x_24 = l_Lean_Syntax_isOfKind(x_18, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_mk_string_unchecked("ident", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
lean_inc(x_18);
x_27 = l_Lean_Syntax_isOfKind(x_18, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_4);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
else
{
x_7 = x_18;
x_8 = x_6;
goto block_14;
}
}
else
{
x_7 = x_18;
x_8 = x_6;
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_array_push(x_4, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg(x_1, x_2, x_12, x_9, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("hole", 4, 4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_mk_string_unchecked("ident", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_1, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_push(x_23, x_21);
lean_ctor_set(x_11, 0, x_24);
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_array_push(x_27, x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_10, 0, x_29);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_32 = x_11;
} else {
 lean_dec_ref(x_11);
 x_32 = lean_box(0);
}
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_31);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_1, x_38);
x_41 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_40, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_52 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_53 = lean_mk_empty_array_with_capacity(x_38);
x_54 = lean_array_push(x_53, x_50);
x_55 = lean_array_size(x_52);
x_56 = lean_usize_of_nat(x_38);
x_57 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(x_52, x_55, x_56, x_54, x_2, x_49);
lean_dec(x_52);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("x", 1, 1);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_addMacroScope(x_10, x_4, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_1, x_7, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_mkIdentFrom(x_1, x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_mkExplicitBinder(x_6, x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_mkHole(x_7, x_12);
lean_dec(x_7);
x_14 = l_Lean_Elab_Term_mkExplicitBinder(x_8, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_10, x_4, x_14);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_4);
x_9 = l_Lean_Macro_resolveGlobalName(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_box(1);
x_14 = l_List_isEmpty___redArg(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
if (x_6 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
lean_free_object(x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_box(1);
x_22 = l_List_isEmpty___redArg(x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
if (x_6 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
lean_inc(x_8);
x_12 = l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(x_1, x_11, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = lean_unbox(x_10);
x_19 = l_Lean_mkHole(x_1, x_18);
lean_inc(x_14);
x_20 = l_Lean_Elab_Term_mkExplicitBinder(x_14, x_19);
x_21 = lean_array_push(x_3, x_20);
lean_inc(x_8);
x_22 = l_Lean_Elab_Term_expandFunBinders_loop(x_4, x_5, x_17, x_21, x_8, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 5);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_unbox(x_10);
x_34 = l_Lean_SourceInfo_fromRef(x_32, x_33);
lean_dec(x_32);
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Parser", 6, 6);
x_37 = lean_mk_string_unchecked("Term", 4, 4);
x_38 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_39 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_38);
lean_inc(x_34);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_34);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = l_Array_mkArray0(lean_box(0));
lean_inc(x_41);
lean_inc(x_34);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_45 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_44);
lean_inc(x_43);
lean_inc(x_34);
x_46 = l_Lean_Syntax_node2(x_34, x_45, x_43, x_14);
lean_inc(x_41);
lean_inc(x_34);
x_47 = l_Lean_Syntax_node1(x_34, x_41, x_46);
x_48 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_34);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_51 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_50);
x_52 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_53 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_52);
x_54 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_34);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_41);
lean_inc(x_34);
x_56 = l_Lean_Syntax_node1(x_34, x_41, x_1);
lean_inc(x_41);
lean_inc(x_34);
x_57 = l_Lean_Syntax_node1(x_34, x_41, x_56);
x_58 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_34);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_34);
x_60 = l_Lean_Syntax_node4(x_34, x_53, x_55, x_57, x_59, x_30);
lean_inc(x_34);
x_61 = l_Lean_Syntax_node1(x_34, x_41, x_60);
lean_inc(x_34);
x_62 = l_Lean_Syntax_node1(x_34, x_51, x_61);
lean_inc(x_43);
x_63 = l_Lean_Syntax_node6(x_34, x_39, x_12, x_43, x_43, x_47, x_49, x_62);
x_64 = lean_box(x_6);
lean_ctor_set(x_24, 1, x_64);
lean_ctor_set(x_24, 0, x_63);
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_65 = lean_ctor_get(x_24, 0);
lean_inc(x_65);
lean_dec(x_24);
x_66 = lean_ctor_get(x_8, 5);
lean_inc(x_66);
lean_dec(x_8);
x_67 = lean_unbox(x_10);
x_68 = l_Lean_SourceInfo_fromRef(x_66, x_67);
lean_dec(x_66);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Parser", 6, 6);
x_71 = lean_mk_string_unchecked("Term", 4, 4);
x_72 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
x_73 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_72);
lean_inc(x_68);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_72);
lean_ctor_set(x_12, 0, x_68);
x_74 = lean_mk_string_unchecked("null", 4, 4);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = l_Array_mkArray0(lean_box(0));
lean_inc(x_75);
lean_inc(x_68);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
x_79 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_78);
lean_inc(x_77);
lean_inc(x_68);
x_80 = l_Lean_Syntax_node2(x_68, x_79, x_77, x_14);
lean_inc(x_75);
lean_inc(x_68);
x_81 = l_Lean_Syntax_node1(x_68, x_75, x_80);
x_82 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_68);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
x_85 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_84);
x_86 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_87 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_86);
x_88 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_68);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_68);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_75);
lean_inc(x_68);
x_90 = l_Lean_Syntax_node1(x_68, x_75, x_1);
lean_inc(x_75);
lean_inc(x_68);
x_91 = l_Lean_Syntax_node1(x_68, x_75, x_90);
x_92 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_68);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_68);
x_94 = l_Lean_Syntax_node4(x_68, x_87, x_89, x_91, x_93, x_65);
lean_inc(x_68);
x_95 = l_Lean_Syntax_node1(x_68, x_75, x_94);
lean_inc(x_68);
x_96 = l_Lean_Syntax_node1(x_68, x_85, x_95);
lean_inc(x_77);
x_97 = l_Lean_Syntax_node6(x_68, x_73, x_12, x_77, x_77, x_81, x_83, x_96);
x_98 = lean_box(x_6);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_23, 1, x_99);
return x_22;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_100 = lean_ctor_get(x_23, 0);
lean_inc(x_100);
lean_dec(x_23);
x_101 = lean_ctor_get(x_24, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_102 = x_24;
} else {
 lean_dec_ref(x_24);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_8, 5);
lean_inc(x_103);
lean_dec(x_8);
x_104 = lean_unbox(x_10);
x_105 = l_Lean_SourceInfo_fromRef(x_103, x_104);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("Lean", 4, 4);
x_107 = lean_mk_string_unchecked("Parser", 6, 6);
x_108 = lean_mk_string_unchecked("Term", 4, 4);
x_109 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_110 = l_Lean_Name_mkStr4(x_106, x_107, x_108, x_109);
lean_inc(x_105);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_109);
lean_ctor_set(x_12, 0, x_105);
x_111 = lean_mk_string_unchecked("null", 4, 4);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = l_Array_mkArray0(lean_box(0));
lean_inc(x_112);
lean_inc(x_105);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_116 = l_Lean_Name_mkStr4(x_106, x_107, x_108, x_115);
lean_inc(x_114);
lean_inc(x_105);
x_117 = l_Lean_Syntax_node2(x_105, x_116, x_114, x_14);
lean_inc(x_112);
lean_inc(x_105);
x_118 = l_Lean_Syntax_node1(x_105, x_112, x_117);
x_119 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_105);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_105);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_122 = l_Lean_Name_mkStr4(x_106, x_107, x_108, x_121);
x_123 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_124 = l_Lean_Name_mkStr4(x_106, x_107, x_108, x_123);
x_125 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_105);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_105);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_112);
lean_inc(x_105);
x_127 = l_Lean_Syntax_node1(x_105, x_112, x_1);
lean_inc(x_112);
lean_inc(x_105);
x_128 = l_Lean_Syntax_node1(x_105, x_112, x_127);
x_129 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_105);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_105);
x_131 = l_Lean_Syntax_node4(x_105, x_124, x_126, x_128, x_130, x_101);
lean_inc(x_105);
x_132 = l_Lean_Syntax_node1(x_105, x_112, x_131);
lean_inc(x_105);
x_133 = l_Lean_Syntax_node1(x_105, x_122, x_132);
lean_inc(x_114);
x_134 = l_Lean_Syntax_node6(x_105, x_110, x_12, x_114, x_114, x_118, x_120, x_133);
x_135 = lean_box(x_6);
if (lean_is_scalar(x_102)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_102;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_100);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_22, 0, x_137);
return x_22;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_138 = lean_ctor_get(x_22, 1);
lean_inc(x_138);
lean_dec(x_22);
x_139 = lean_ctor_get(x_23, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_140 = x_23;
} else {
 lean_dec_ref(x_23);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_24, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_142 = x_24;
} else {
 lean_dec_ref(x_24);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_8, 5);
lean_inc(x_143);
lean_dec(x_8);
x_144 = lean_unbox(x_10);
x_145 = l_Lean_SourceInfo_fromRef(x_143, x_144);
lean_dec(x_143);
x_146 = lean_mk_string_unchecked("Lean", 4, 4);
x_147 = lean_mk_string_unchecked("Parser", 6, 6);
x_148 = lean_mk_string_unchecked("Term", 4, 4);
x_149 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
x_150 = l_Lean_Name_mkStr4(x_146, x_147, x_148, x_149);
lean_inc(x_145);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_149);
lean_ctor_set(x_12, 0, x_145);
x_151 = lean_mk_string_unchecked("null", 4, 4);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = l_Array_mkArray0(lean_box(0));
lean_inc(x_152);
lean_inc(x_145);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
x_156 = l_Lean_Name_mkStr4(x_146, x_147, x_148, x_155);
lean_inc(x_154);
lean_inc(x_145);
x_157 = l_Lean_Syntax_node2(x_145, x_156, x_154, x_14);
lean_inc(x_152);
lean_inc(x_145);
x_158 = l_Lean_Syntax_node1(x_145, x_152, x_157);
x_159 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_145);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
x_162 = l_Lean_Name_mkStr4(x_146, x_147, x_148, x_161);
x_163 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_164 = l_Lean_Name_mkStr4(x_146, x_147, x_148, x_163);
x_165 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_145);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_145);
lean_ctor_set(x_166, 1, x_165);
lean_inc(x_152);
lean_inc(x_145);
x_167 = l_Lean_Syntax_node1(x_145, x_152, x_1);
lean_inc(x_152);
lean_inc(x_145);
x_168 = l_Lean_Syntax_node1(x_145, x_152, x_167);
x_169 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_145);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_145);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_145);
x_171 = l_Lean_Syntax_node4(x_145, x_164, x_166, x_168, x_170, x_141);
lean_inc(x_145);
x_172 = l_Lean_Syntax_node1(x_145, x_152, x_171);
lean_inc(x_145);
x_173 = l_Lean_Syntax_node1(x_145, x_162, x_172);
lean_inc(x_154);
x_174 = l_Lean_Syntax_node6(x_145, x_150, x_12, x_154, x_154, x_158, x_160, x_173);
x_175 = lean_box(x_6);
if (lean_is_scalar(x_142)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_142;
}
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
if (lean_is_scalar(x_140)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_140;
}
lean_ctor_set(x_177, 0, x_139);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_138);
return x_178;
}
}
else
{
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_12, 0);
x_180 = lean_ctor_get(x_12, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_12);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_2, x_181);
x_183 = lean_unbox(x_10);
x_184 = l_Lean_mkHole(x_1, x_183);
lean_inc(x_179);
x_185 = l_Lean_Elab_Term_mkExplicitBinder(x_179, x_184);
x_186 = lean_array_push(x_3, x_185);
lean_inc(x_8);
x_187 = l_Lean_Elab_Term_expandFunBinders_loop(x_4, x_5, x_182, x_186, x_8, x_180);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_195 = x_189;
} else {
 lean_dec_ref(x_189);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_8, 5);
lean_inc(x_196);
lean_dec(x_8);
x_197 = lean_unbox(x_10);
x_198 = l_Lean_SourceInfo_fromRef(x_196, x_197);
lean_dec(x_196);
x_199 = lean_mk_string_unchecked("Lean", 4, 4);
x_200 = lean_mk_string_unchecked("Parser", 6, 6);
x_201 = lean_mk_string_unchecked("Term", 4, 4);
x_202 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_203 = l_Lean_Name_mkStr4(x_199, x_200, x_201, x_202);
lean_inc(x_198);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_mk_string_unchecked("null", 4, 4);
x_206 = l_Lean_Name_mkStr1(x_205);
x_207 = l_Array_mkArray0(lean_box(0));
lean_inc(x_206);
lean_inc(x_198);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_198);
lean_ctor_set(x_208, 1, x_206);
lean_ctor_set(x_208, 2, x_207);
x_209 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_210 = l_Lean_Name_mkStr4(x_199, x_200, x_201, x_209);
lean_inc(x_208);
lean_inc(x_198);
x_211 = l_Lean_Syntax_node2(x_198, x_210, x_208, x_179);
lean_inc(x_206);
lean_inc(x_198);
x_212 = l_Lean_Syntax_node1(x_198, x_206, x_211);
x_213 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_198);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_198);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_216 = l_Lean_Name_mkStr4(x_199, x_200, x_201, x_215);
x_217 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_218 = l_Lean_Name_mkStr4(x_199, x_200, x_201, x_217);
x_219 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_198);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_198);
lean_ctor_set(x_220, 1, x_219);
lean_inc(x_206);
lean_inc(x_198);
x_221 = l_Lean_Syntax_node1(x_198, x_206, x_1);
lean_inc(x_206);
lean_inc(x_198);
x_222 = l_Lean_Syntax_node1(x_198, x_206, x_221);
x_223 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_198);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_198);
lean_ctor_set(x_224, 1, x_223);
lean_inc(x_198);
x_225 = l_Lean_Syntax_node4(x_198, x_218, x_220, x_222, x_224, x_194);
lean_inc(x_198);
x_226 = l_Lean_Syntax_node1(x_198, x_206, x_225);
lean_inc(x_198);
x_227 = l_Lean_Syntax_node1(x_198, x_216, x_226);
lean_inc(x_208);
x_228 = l_Lean_Syntax_node6(x_198, x_203, x_204, x_208, x_208, x_212, x_214, x_227);
x_229 = lean_box(x_6);
if (lean_is_scalar(x_195)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_195;
}
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
if (lean_is_scalar(x_193)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_193;
}
lean_ctor_set(x_231, 0, x_192);
lean_ctor_set(x_231, 1, x_230);
if (lean_is_scalar(x_191)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_191;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_190);
return x_232;
}
else
{
lean_dec(x_179);
lean_dec(x_8);
lean_dec(x_1);
return x_187;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_array_push(x_2, x_3);
x_12 = l_Lean_Elab_Term_expandFunBinders_loop(x_4, x_5, x_10, x_11, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_1, x_3);
x_14 = lean_box(x_8);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___boxed), 9, 6);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_getKind(x_13);
x_17 = lean_box(0);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_17, x_5, x_6);
return x_18;
}
case 1:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("ident", 5, 5);
x_22 = lean_string_dec_eq(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Name_str___override(x_17, x_20);
x_24 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_23, x_5, x_6);
lean_dec(x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_25, x_5, x_6);
lean_dec(x_3);
return x_26;
}
}
case 1:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lean_Name_str___override(x_17, x_29);
x_31 = l_Lean_Name_str___override(x_30, x_28);
x_32 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_31, x_5, x_6);
lean_dec(x_31);
return x_32;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
lean_inc(x_36);
x_37 = l_Lean_Name_str___override(x_17, x_36);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_Name_str___override(x_37, x_34);
x_39 = l_Lean_Name_str___override(x_38, x_33);
x_40 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_39, x_5, x_6);
lean_dec(x_39);
return x_40;
}
case 1:
{
lean_object* x_41; 
lean_dec(x_37);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_mk_string_unchecked("Lean", 4, 4);
x_44 = lean_string_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l_Lean_Name_str___override(x_17, x_42);
x_46 = l_Lean_Name_str___override(x_45, x_36);
x_47 = l_Lean_Name_str___override(x_46, x_34);
x_48 = l_Lean_Name_str___override(x_47, x_33);
x_49 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_48, x_5, x_6);
lean_dec(x_48);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_42);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_string_dec_eq(x_36, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = l_Lean_Name_str___override(x_17, x_43);
x_53 = l_Lean_Name_str___override(x_52, x_36);
x_54 = l_Lean_Name_str___override(x_53, x_34);
x_55 = l_Lean_Name_str___override(x_54, x_33);
x_56 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_55, x_5, x_6);
lean_dec(x_55);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_36);
x_57 = lean_mk_string_unchecked("Term", 4, 4);
x_58 = lean_string_dec_eq(x_34, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Lean_Name_str___override(x_17, x_43);
x_60 = l_Lean_Name_str___override(x_59, x_50);
x_61 = l_Lean_Name_str___override(x_60, x_34);
x_62 = l_Lean_Name_str___override(x_61, x_33);
x_63 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_62, x_5, x_6);
lean_dec(x_62);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_34);
x_64 = lean_mk_string_unchecked("implicitBinder", 14, 14);
x_65 = lean_string_dec_eq(x_33, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
x_67 = lean_string_dec_eq(x_33, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_mk_string_unchecked("instBinder", 10, 10);
x_69 = lean_string_dec_eq(x_33, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_mk_string_unchecked("explicitBinder", 14, 14);
x_71 = lean_string_dec_eq(x_33, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_mk_string_unchecked("hole", 4, 4);
x_73 = lean_string_dec_eq(x_33, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_mk_string_unchecked("paren", 5, 5);
x_75 = lean_string_dec_eq(x_33, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_77 = lean_string_dec_eq(x_33, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = l_Lean_Name_str___override(x_17, x_43);
x_79 = l_Lean_Name_str___override(x_78, x_50);
x_80 = l_Lean_Name_str___override(x_79, x_57);
x_81 = l_Lean_Name_str___override(x_80, x_33);
x_82 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_81, x_5, x_6);
lean_dec(x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_83 = lean_unsigned_to_nat(1u);
x_84 = l_Lean_Syntax_getArg(x_13, x_83);
x_101 = lean_unsigned_to_nat(3u);
x_102 = l_Lean_Syntax_getArg(x_13, x_101);
x_103 = l_Lean_Syntax_getOptional_x3f(x_102);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = l_Lean_mkHole(x_13, x_75);
x_85 = x_104;
goto block_100;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_85 = x_105;
goto block_100;
}
block_100:
{
lean_object* x_86; lean_object* x_87; 
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_84, x_5, x_6);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
x_90 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_89, x_5, x_88);
lean_dec(x_3);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; lean_object* x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_13);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_nat_add(x_3, x_83);
lean_dec(x_3);
x_94 = lean_array_size(x_92);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_usize_of_nat(x_95);
x_97 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(x_85, x_94, x_96, x_92);
x_98 = l_Array_append(lean_box(0), x_4, x_97);
lean_dec(x_97);
x_3 = x_93;
x_4 = x_98;
x_6 = x_91;
goto _start;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_106 = lean_unsigned_to_nat(1u);
x_107 = l_Lean_Syntax_getArg(x_13, x_106);
x_108 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_107, x_5, x_6);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
x_112 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_111, x_5, x_110);
lean_dec(x_3);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_124; uint8_t x_125; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_unsigned_to_nat(0u);
x_124 = lean_array_get_size(x_114);
x_125 = lean_nat_dec_lt(x_115, x_124);
if (x_125 == 0)
{
lean_dec(x_124);
lean_dec(x_13);
x_116 = x_113;
goto block_123;
}
else
{
if (x_125 == 0)
{
lean_dec(x_124);
lean_dec(x_13);
x_116 = x_113;
goto block_123;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
x_126 = lean_usize_of_nat(x_115);
x_127 = lean_usize_of_nat(x_124);
lean_dec(x_124);
lean_inc(x_5);
x_128 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(x_114, x_126, x_127, x_5, x_113);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_13);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_116 = x_131;
goto block_123;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_114);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_box(0);
x_134 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_133, x_5, x_132);
lean_dec(x_3);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_114);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_128);
if (x_135 == 0)
{
return x_128;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
block_123:
{
lean_object* x_117; size_t x_118; size_t x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_nat_add(x_3, x_106);
x_118 = lean_array_size(x_114);
x_119 = lean_usize_of_nat(x_115);
x_120 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(x_1, x_3, x_118, x_119, x_114);
lean_dec(x_3);
x_121 = l_Array_append(lean_box(0), x_4, x_120);
lean_dec(x_120);
x_3 = x_117;
x_4 = x_121;
x_6 = x_116;
goto _start;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_139 = lean_box(0);
x_140 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_139, x_5, x_6);
lean_dec(x_3);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_141, x_5, x_6);
lean_dec(x_3);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_143 = lean_box(0);
x_144 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_143, x_5, x_6);
lean_dec(x_3);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_145 = lean_box(0);
x_146 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_145, x_5, x_6);
lean_dec(x_3);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_15);
x_147 = lean_box(0);
x_148 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_3, x_4, x_13, x_1, x_2, x_147, x_5, x_6);
lean_dec(x_3);
return x_148;
}
}
}
}
}
case 1:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_35, 1);
lean_inc(x_149);
lean_dec(x_35);
x_150 = lean_ctor_get(x_41, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_41, 1);
lean_inc(x_151);
lean_dec(x_41);
x_152 = l_Lean_Name_str___override(x_150, x_151);
x_153 = l_Lean_Name_str___override(x_152, x_149);
x_154 = l_Lean_Name_str___override(x_153, x_36);
x_155 = l_Lean_Name_str___override(x_154, x_34);
x_156 = l_Lean_Name_str___override(x_155, x_33);
x_157 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_156, x_5, x_6);
lean_dec(x_156);
return x_157;
}
default: 
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_35, 1);
lean_inc(x_158);
lean_dec(x_35);
x_159 = lean_ctor_get(x_41, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_41, 1);
lean_inc(x_160);
lean_dec(x_41);
x_161 = l_Lean_Name_num___override(x_159, x_160);
x_162 = l_Lean_Name_str___override(x_161, x_158);
x_163 = l_Lean_Name_str___override(x_162, x_36);
x_164 = l_Lean_Name_str___override(x_163, x_34);
x_165 = l_Lean_Name_str___override(x_164, x_33);
x_166 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_165, x_5, x_6);
lean_dec(x_165);
return x_166;
}
}
}
default: 
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_37);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_35, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_35, 1);
lean_inc(x_168);
lean_dec(x_35);
x_169 = l_Lean_Name_num___override(x_167, x_168);
x_170 = l_Lean_Name_str___override(x_169, x_36);
x_171 = l_Lean_Name_str___override(x_170, x_34);
x_172 = l_Lean_Name_str___override(x_171, x_33);
x_173 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_172, x_5, x_6);
lean_dec(x_172);
return x_173;
}
}
}
default: 
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_16, 1);
lean_inc(x_174);
lean_dec(x_16);
x_175 = lean_ctor_get(x_19, 1);
lean_inc(x_175);
lean_dec(x_19);
x_176 = lean_ctor_get(x_27, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_27, 1);
lean_inc(x_177);
lean_dec(x_27);
x_178 = l_Lean_Name_num___override(x_176, x_177);
x_179 = l_Lean_Name_str___override(x_178, x_175);
x_180 = l_Lean_Name_str___override(x_179, x_174);
x_181 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_180, x_5, x_6);
lean_dec(x_180);
return x_181;
}
}
}
default: 
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_16, 1);
lean_inc(x_182);
lean_dec(x_16);
x_183 = lean_ctor_get(x_19, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_19, 1);
lean_inc(x_184);
lean_dec(x_19);
x_185 = l_Lean_Name_num___override(x_183, x_184);
x_186 = l_Lean_Name_str___override(x_185, x_182);
x_187 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_186, x_5, x_6);
lean_dec(x_186);
return x_187;
}
}
}
default: 
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_16, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_16, 1);
lean_inc(x_189);
lean_dec(x_16);
x_190 = l_Lean_Name_num___override(x_188, x_189);
x_191 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_15, x_190, x_5, x_6);
lean_dec(x_190);
return x_191;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_expandFunBinders_loop___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnfForall(x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_isExprDefEq(x_2, x_16, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_expr_instantiate1(x_17, x_1);
lean_dec(x_17);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
lean_dec(x_3);
lean_ctor_set(x_9, 0, x_21);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_9);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_expr_instantiate1(x_17, x_1);
lean_dec(x_17);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_dec(x_3);
lean_ctor_set(x_9, 0, x_27);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_free_object(x_9);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_13, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_13, 0, x_43);
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_9, 0);
lean_inc(x_55);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_whnfForall(x_55, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 7)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_Meta_isExprDefEq(x_2, x_59, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_expr_instantiate1(x_60, x_1);
lean_dec(x_60);
x_65 = lean_ctor_get(x_3, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_64);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_69, 3, x_68);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
lean_dec(x_3);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 2);
lean_inc(x_79);
lean_dec(x_3);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_80);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_56, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_85 = x_56;
} else {
 lean_dec_ref(x_56);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_nat_add(x_13, x_7);
lean_inc(x_12);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 7);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Name_num___override(x_12, x_13);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Name_num___override(x_12, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_nat_add(x_33, x_7);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 7);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_43, 7, x_42);
x_44 = lean_st_ref_set(x_1, x_43, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Name_num___override(x_32, x_33);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_16 = l_Lean_Elab_Term_elabType(x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_17, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_Expr_fvar___override(x_22);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = l_Lean_Syntax_getId(x_25);
x_27 = l_Lean_Elab_Term_kindOfBinderName(x_26);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_17);
lean_inc(x_3);
x_29 = l_Lean_LocalContext_mkLocalDecl(x_3, x_22, x_26, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_box(0);
lean_inc(x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_24);
x_34 = l_Lean_Elab_Term_addTermInfo_x27(x_30, x_24, x_31, x_32, x_33, x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_inc(x_24);
x_37 = lean_array_push(x_36, x_24);
x_38 = lean_ctor_get(x_5, 3);
lean_inc(x_38);
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_ctor_get(x_13, 5);
lean_inc(x_40);
x_41 = l_Lean_replaceRef(x_25, x_40);
lean_dec(x_40);
lean_dec(x_25);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_13, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_13, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_13, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 10);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_13, sizeof(void*)*13);
x_53 = lean_ctor_get(x_13, 11);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_13, sizeof(void*)*13 + 1);
x_55 = lean_ctor_get(x_13, 12);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_41);
lean_ctor_set(x_56, 6, x_47);
lean_ctor_set(x_56, 7, x_48);
lean_ctor_set(x_56, 8, x_49);
lean_ctor_set(x_56, 9, x_50);
lean_ctor_set(x_56, 10, x_51);
lean_ctor_set(x_56, 11, x_53);
lean_ctor_set(x_56, 12, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*13, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*13 + 1, x_54);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_17);
x_57 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_24, x_17, x_39, x_11, x_12, x_56, x_14, x_35);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_61 = l_Lean_Meta_isClass_x3f(x_17, x_11, x_12, x_13, x_14, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 3);
lean_inc(x_66);
lean_dec(x_59);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_29);
lean_inc(x_64);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_29);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_57);
lean_dec(x_29);
lean_dec(x_24);
x_68 = x_9;
x_69 = x_10;
x_70 = x_11;
x_71 = x_12;
x_72 = x_13;
x_73 = x_14;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_box(x_27);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_67);
x_79 = lean_ctor_get(x_62, 0);
lean_inc(x_79);
lean_dec(x_62);
lean_ctor_set(x_57, 1, x_24);
lean_ctor_set(x_57, 0, x_79);
x_80 = lean_array_push(x_65, x_57);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_7, x_81);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_29);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_66);
x_84 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_8, x_82, x_83, x_9, x_10, x_11, x_12, x_13, x_14, x_63);
lean_dec(x_13);
lean_dec(x_11);
return x_84;
}
else
{
lean_dec(x_78);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_free_object(x_57);
lean_dec(x_29);
lean_dec(x_24);
x_68 = x_9;
x_69 = x_10;
x_70 = x_11;
x_71 = x_12;
x_72 = x_13;
x_73 = x_14;
goto block_77;
}
}
block_77:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_7, x_74);
x_76 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_8, x_75, x_67, x_68, x_69, x_70, x_71, x_72, x_73, x_63);
lean_dec(x_72);
lean_dec(x_70);
return x_76;
}
}
else
{
uint8_t x_85; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_61);
if (x_85 == 0)
{
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_61, 0);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_61);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_57, 0);
x_90 = lean_ctor_get(x_57, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_57);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_91 = l_Lean_Meta_isClass_x3f(x_17, x_11, x_12, x_13, x_14, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 3);
lean_inc(x_96);
lean_dec(x_89);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_29);
lean_inc(x_94);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_29);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
if (lean_obj_tag(x_92) == 0)
{
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_29);
lean_dec(x_24);
x_98 = x_9;
x_99 = x_10;
x_100 = x_11;
x_101 = x_12;
x_102 = x_13;
x_103 = x_14;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_box(x_27);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_97);
x_109 = lean_ctor_get(x_92, 0);
lean_inc(x_109);
lean_dec(x_92);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_24);
x_111 = lean_array_push(x_95, x_110);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_7, x_112);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_94);
lean_ctor_set(x_114, 1, x_29);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_96);
x_115 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_8, x_113, x_114, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
lean_dec(x_13);
lean_dec(x_11);
return x_115;
}
else
{
lean_dec(x_108);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_24);
x_98 = x_9;
x_99 = x_10;
x_100 = x_11;
x_101 = x_12;
x_102 = x_13;
x_103 = x_14;
goto block_107;
}
}
block_107:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_7, x_104);
x_106 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_8, x_105, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_93);
lean_dec(x_102);
lean_dec(x_100);
return x_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = lean_ctor_get(x_91, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_91, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_118 = x_91;
} else {
 lean_dec_ref(x_91);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_57;
}
}
else
{
uint8_t x_120; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_34);
if (x_120 == 0)
{
return x_34;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_34, 0);
x_122 = lean_ctor_get(x_34, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_34);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_16);
if (x_124 == 0)
{
return x_16;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_16, 0);
x_126 = lean_ctor_get(x_16, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_16);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
x_20 = lean_box(x_12);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed), 15, 8);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_3);
lean_closure_set(x_21, 5, x_19);
lean_closure_set(x_21, 6, x_2);
lean_closure_set(x_21, 7, x_1);
x_22 = lean_ctor_get(x_8, 5);
x_23 = l_Lean_replaceRef(x_17, x_22);
lean_dec(x_17);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 6);
x_30 = lean_ctor_get(x_8, 7);
x_31 = lean_ctor_get(x_8, 8);
x_32 = lean_ctor_get(x_8, 9);
x_33 = lean_ctor_get(x_8, 10);
x_34 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_35 = lean_ctor_get(x_8, 11);
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_37 = lean_ctor_get(x_8, 12);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_38 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_23);
lean_ctor_set(x_38, 6, x_29);
lean_ctor_set(x_38, 7, x_30);
lean_ctor_set(x_38, 8, x_31);
lean_ctor_set(x_38, 9, x_32);
lean_ctor_set(x_38, 10, x_33);
lean_ctor_set(x_38, 11, x_35);
lean_ctor_set(x_38, 12, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_36);
x_39 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_18, x_19, x_21, x_4, x_5, x_6, x_7, x_38, x_9, x_16);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_20;
x_10 = x_21;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_19;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Meta_getLocalInstances___redArg(x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 3);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_apply_2(x_3, x_24, x_25);
x_27 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_22, x_23, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_apply_9(x_3, x_33, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabFunBinders___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabFunBinders___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabFunBinders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_mk_string_unchecked("letRecDecl", 10, 10);
x_11 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_9);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("whereDecls", 10, 10);
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_5, 0, x_23);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_26 = l_Lean_Syntax_isOfKind(x_1, x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_6 = x_28;
goto block_11;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_array_uget(x_2, x_3);
x_33 = lean_array_push(x_30, x_32);
x_34 = lean_box(x_16);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_array_uget(x_2, x_3);
x_37 = lean_array_push(x_35, x_36);
x_38 = lean_box(x_16);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_6 = x_39;
goto block_11;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_47 = lean_mk_string_unchecked("whereDecls", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_48 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_47);
lean_inc(x_1);
x_49 = l_Lean_Syntax_isOfKind(x_1, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l_Lean_Macro_throwUnsupported(lean_box(0), x_3, x_4);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Syntax_getArg(x_1, x_51);
x_53 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_54 = l_Array_empty(lean_box(0));
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_53);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_1);
x_8 = x_54;
goto block_46;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_56, x_56);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_1);
x_8 = x_54;
goto block_46;
}
else
{
lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
x_61 = lean_usize_of_nat(x_55);
x_62 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_63 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1(x_1, x_53, x_61, x_62, x_60);
lean_dec(x_53);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_8 = x_64;
goto block_46;
}
}
}
block_46:
{
size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_9, x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = l_Lean_Macro_throwUnsupported(lean_box(0), x_3, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_box(0);
x_20 = lean_mk_string_unchecked("letrec", 6, 6);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_20);
x_22 = lean_mk_string_unchecked("group", 5, 5);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_18);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_18);
x_28 = l_Lean_Syntax_node2(x_18, x_23, x_25, x_27);
x_29 = lean_mk_string_unchecked("letRecDecls", 11, 11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_29);
x_31 = lean_mk_string_unchecked("null", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Array_mkArray0(lean_box(0));
x_34 = lean_mk_string_unchecked("letRecDecl", 10, 10);
x_35 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_19);
x_37 = lean_mk_string_unchecked(",", 1, 1);
x_38 = l_Lean_Syntax_TSepArray_ofElems(x_36, x_37, x_14);
lean_dec(x_14);
lean_dec(x_36);
x_39 = l_Array_append(lean_box(0), x_33, x_38);
lean_dec(x_38);
lean_inc(x_18);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_18);
x_41 = l_Lean_Syntax_node1(x_18, x_30, x_40);
x_42 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_18);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Syntax_node4(x_18, x_21, x_28, x_41, x_43, x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandWhereDecls_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isNone(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Elab_Term_expandWhereDecls(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_mk_string_unchecked("null", 4, 4);
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_dec(x_6);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_1, 5);
x_9 = l_Lean_Name_mkStr1(x_6);
x_10 = l_Array_mkArray0(lean_box(0));
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = l_Lean_SourceInfo_fromRef(x_8, x_2);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_box(0);
lean_inc(x_5);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = lean_mk_string_unchecked("matchDiscr", 10, 10);
x_19 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_18);
x_20 = lean_array_uget(x_5, x_4);
lean_dec(x_5);
x_21 = l_Lean_Syntax_node2(x_14, x_19, x_15, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_4, x_23);
x_25 = lean_array_uset(x_17, x_4, x_21);
x_4 = x_24;
x_5 = x_25;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_mk_string_unchecked("null", 4, 4);
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_box(0);
x_9 = l_Lean_Name_mkStr1(x_5);
x_10 = l_Array_mkArray0(lean_box(0));
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_unbox(x_8);
x_14 = l_Lean_SourceInfo_fromRef(x_7, x_13);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_box(0);
lean_inc(x_4);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = lean_mk_string_unchecked("Term", 4, 4);
x_19 = lean_mk_string_unchecked("matchDiscr", 10, 10);
x_20 = l_Lean_Name_mkStr4(x_11, x_12, x_18, x_19);
x_21 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
x_22 = l_Lean_Syntax_node2(x_14, x_20, x_15, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_26 = lean_array_uset(x_17, x_3, x_22);
x_3 = x_25;
x_4 = x_26;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 1)
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_11 = lean_ctor_get(x_7, 5);
lean_inc(x_11);
x_12 = l_Lean_SourceInfo_fromRef(x_11, x_2);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Term", 4, 4);
x_16 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Array_mkArray0(lean_box(0));
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_size(x_5);
x_24 = lean_usize_of_nat(x_9);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(x_7, x_2, x_23, x_24, x_5);
x_26 = lean_mk_string_unchecked(",", 1, 1);
x_27 = l_Lean_mkAtom(x_26);
x_28 = l_Lean_mkSepArray(x_25, x_27);
lean_dec(x_25);
x_29 = l_Array_append(lean_box(0), x_21, x_28);
lean_dec(x_28);
lean_inc(x_12);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_12);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_22);
x_33 = l_Lean_Syntax_node6(x_12, x_17, x_18, x_22, x_22, x_30, x_32, x_1);
x_34 = l_Lean_Elab_Term_clearInMatch(x_33, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
x_35 = lean_ctor_get(x_7, 5);
lean_inc(x_35);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_SourceInfo_fromRef(x_35, x_37);
lean_dec(x_35);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Parser", 6, 6);
x_41 = lean_mk_string_unchecked("Tactic", 6, 6);
x_42 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_42);
x_43 = l_Lean_Name_mkStr4(x_39, x_40, x_41, x_42);
lean_inc(x_38);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_mk_string_unchecked("null", 4, 4);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = l_Array_mkArray0(lean_box(0));
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_38);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_array_size(x_5);
x_50 = lean_usize_of_nat(x_9);
x_51 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(x_7, x_49, x_50, x_5);
lean_dec(x_7);
x_52 = lean_mk_string_unchecked(",", 1, 1);
x_53 = l_Lean_mkAtom(x_52);
x_54 = l_Lean_mkSepArray(x_51, x_53);
lean_dec(x_51);
x_55 = l_Array_append(lean_box(0), x_47, x_54);
lean_dec(x_54);
lean_inc(x_38);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_38);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_48);
x_59 = l_Lean_Syntax_node6(x_38, x_43, x_44, x_48, x_48, x_56, x_58, x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_61 = lean_ctor_get(x_8, 0);
lean_inc(x_61);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_61, x_62);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_dec(x_8);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
lean_dec(x_7);
lean_inc(x_70);
lean_inc(x_61);
lean_inc(x_67);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_61);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_70);
x_72 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_70, x_71, x_65);
lean_dec(x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_77, x_71, x_78);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
x_83 = lean_mk_string_unchecked("x", 1, 1);
lean_inc(x_83);
x_84 = l_Lean_Name_mkStr1(x_83);
x_85 = lean_nat_sub(x_4, x_62);
x_86 = l_String_toSubstring_x27(x_83);
x_87 = l_Lean_addMacroScope(x_67, x_84, x_61);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_73);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Parser", 6, 6);
x_92 = lean_mk_string_unchecked("Term", 4, 4);
x_93 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_94 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_93);
x_95 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_95);
lean_inc(x_81);
lean_ctor_set_tag(x_79, 2);
lean_ctor_set(x_79, 1, x_95);
lean_inc(x_89);
lean_inc(x_94);
x_96 = l_Lean_Syntax_node2(x_81, x_94, x_79, x_89);
x_97 = lean_array_push(x_5, x_96);
lean_inc(x_89);
x_98 = lean_array_push(x_6, x_89);
lean_inc(x_71);
x_99 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_85, x_97, x_98, x_71, x_82);
lean_dec(x_85);
if (x_2 == 0)
{
if (x_3 == 0)
{
uint8_t x_100; 
lean_dec(x_95);
lean_dec(x_94);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_102);
lean_dec(x_71);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = l_Lean_SourceInfo_fromRef(x_105, x_3);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_107);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_108 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_107);
lean_inc(x_106);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_107);
lean_ctor_set(x_99, 0, x_106);
x_109 = lean_mk_string_unchecked("basicFun", 8, 8);
x_110 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_109);
x_111 = lean_mk_string_unchecked("null", 4, 4);
x_112 = l_Lean_Name_mkStr1(x_111);
lean_inc(x_112);
lean_inc(x_106);
x_113 = l_Lean_Syntax_node1(x_106, x_112, x_89);
x_114 = l_Array_mkArray0(lean_box(0));
lean_inc(x_106);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_106);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_116);
lean_ctor_set(x_75, 0, x_106);
lean_inc(x_106);
x_117 = l_Lean_Syntax_node4(x_106, x_110, x_113, x_115, x_75, x_101);
x_118 = l_Lean_Syntax_node2(x_106, x_108, x_99, x_117);
lean_ctor_set(x_103, 0, x_118);
return x_103;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_103, 0);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_103);
x_121 = l_Lean_SourceInfo_fromRef(x_119, x_3);
lean_dec(x_119);
x_122 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_122);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_123 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_122);
lean_inc(x_121);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_122);
lean_ctor_set(x_99, 0, x_121);
x_124 = lean_mk_string_unchecked("basicFun", 8, 8);
x_125 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_124);
x_126 = lean_mk_string_unchecked("null", 4, 4);
x_127 = l_Lean_Name_mkStr1(x_126);
lean_inc(x_127);
lean_inc(x_121);
x_128 = l_Lean_Syntax_node1(x_121, x_127, x_89);
x_129 = l_Array_mkArray0(lean_box(0));
lean_inc(x_121);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_121);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_131);
lean_ctor_set(x_75, 0, x_121);
lean_inc(x_121);
x_132 = l_Lean_Syntax_node4(x_121, x_125, x_128, x_130, x_75, x_101);
x_133 = l_Lean_Syntax_node2(x_121, x_123, x_99, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_135 = lean_ctor_get(x_99, 0);
x_136 = lean_ctor_get(x_99, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_99);
x_137 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_136);
lean_dec(x_71);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
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
x_141 = l_Lean_SourceInfo_fromRef(x_138, x_3);
lean_dec(x_138);
x_142 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_142);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_143 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_142);
lean_inc(x_141);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_mk_string_unchecked("basicFun", 8, 8);
x_146 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_145);
x_147 = lean_mk_string_unchecked("null", 4, 4);
x_148 = l_Lean_Name_mkStr1(x_147);
lean_inc(x_148);
lean_inc(x_141);
x_149 = l_Lean_Syntax_node1(x_141, x_148, x_89);
x_150 = l_Array_mkArray0(lean_box(0));
lean_inc(x_141);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set(x_151, 2, x_150);
x_152 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_141);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_152);
lean_ctor_set(x_75, 0, x_141);
lean_inc(x_141);
x_153 = l_Lean_Syntax_node4(x_141, x_146, x_149, x_151, x_75, x_135);
x_154 = l_Lean_Syntax_node2(x_141, x_143, x_144, x_153);
if (lean_is_scalar(x_140)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_140;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_139);
return x_155;
}
}
else
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_99);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_99, 0);
x_158 = lean_ctor_get(x_99, 1);
x_159 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_158);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_ctor_get(x_159, 1);
x_163 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_161, x_71, x_162);
lean_dec(x_71);
lean_dec(x_161);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_ctor_set_tag(x_159, 2);
lean_ctor_set(x_159, 1, x_95);
lean_ctor_set(x_159, 0, x_165);
x_166 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_166);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_167 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_166);
lean_inc(x_165);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_166);
lean_ctor_set(x_99, 0, x_165);
x_168 = lean_mk_string_unchecked("basicFun", 8, 8);
x_169 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_168);
x_170 = lean_mk_string_unchecked("null", 4, 4);
x_171 = l_Lean_Name_mkStr1(x_170);
lean_inc(x_171);
lean_inc(x_165);
x_172 = l_Lean_Syntax_node1(x_165, x_171, x_89);
x_173 = l_Array_mkArray0(lean_box(0));
lean_inc(x_165);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_165);
lean_ctor_set(x_174, 1, x_171);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_165);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_175);
lean_ctor_set(x_75, 0, x_165);
lean_inc(x_165);
x_176 = l_Lean_Syntax_node4(x_165, x_169, x_172, x_174, x_75, x_157);
lean_inc(x_165);
x_177 = l_Lean_Syntax_node2(x_165, x_167, x_99, x_176);
x_178 = l_Lean_Syntax_node2(x_165, x_94, x_159, x_177);
lean_ctor_set(x_163, 0, x_178);
return x_163;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_163, 0);
x_180 = lean_ctor_get(x_163, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_163);
lean_inc(x_179);
lean_ctor_set_tag(x_159, 2);
lean_ctor_set(x_159, 1, x_95);
lean_ctor_set(x_159, 0, x_179);
x_181 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_181);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_182 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_181);
lean_inc(x_179);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_181);
lean_ctor_set(x_99, 0, x_179);
x_183 = lean_mk_string_unchecked("basicFun", 8, 8);
x_184 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_183);
x_185 = lean_mk_string_unchecked("null", 4, 4);
x_186 = l_Lean_Name_mkStr1(x_185);
lean_inc(x_186);
lean_inc(x_179);
x_187 = l_Lean_Syntax_node1(x_179, x_186, x_89);
x_188 = l_Array_mkArray0(lean_box(0));
lean_inc(x_179);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_179);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_188);
x_190 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_179);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_190);
lean_ctor_set(x_75, 0, x_179);
lean_inc(x_179);
x_191 = l_Lean_Syntax_node4(x_179, x_184, x_187, x_189, x_75, x_157);
lean_inc(x_179);
x_192 = l_Lean_Syntax_node2(x_179, x_182, x_99, x_191);
x_193 = l_Lean_Syntax_node2(x_179, x_94, x_159, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_180);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_195 = lean_ctor_get(x_159, 0);
x_196 = lean_ctor_get(x_159, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_159);
x_197 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_195, x_71, x_196);
lean_dec(x_71);
lean_dec(x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
lean_inc(x_198);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_95);
x_202 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_202);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_203 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_202);
lean_inc(x_198);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_202);
lean_ctor_set(x_99, 0, x_198);
x_204 = lean_mk_string_unchecked("basicFun", 8, 8);
x_205 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_204);
x_206 = lean_mk_string_unchecked("null", 4, 4);
x_207 = l_Lean_Name_mkStr1(x_206);
lean_inc(x_207);
lean_inc(x_198);
x_208 = l_Lean_Syntax_node1(x_198, x_207, x_89);
x_209 = l_Array_mkArray0(lean_box(0));
lean_inc(x_198);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_198);
lean_ctor_set(x_210, 1, x_207);
lean_ctor_set(x_210, 2, x_209);
x_211 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_198);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_211);
lean_ctor_set(x_75, 0, x_198);
lean_inc(x_198);
x_212 = l_Lean_Syntax_node4(x_198, x_205, x_208, x_210, x_75, x_157);
lean_inc(x_198);
x_213 = l_Lean_Syntax_node2(x_198, x_203, x_99, x_212);
x_214 = l_Lean_Syntax_node2(x_198, x_94, x_201, x_213);
if (lean_is_scalar(x_200)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_200;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_199);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_216 = lean_ctor_get(x_99, 0);
x_217 = lean_ctor_get(x_99, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_99);
x_218 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_219, x_71, x_220);
lean_dec(x_71);
lean_dec(x_219);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
lean_inc(x_223);
if (lean_is_scalar(x_221)) {
 x_226 = lean_alloc_ctor(2, 2, 0);
} else {
 x_226 = x_221;
 lean_ctor_set_tag(x_226, 2);
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_95);
x_227 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_227);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_228 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_227);
lean_inc(x_223);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_mk_string_unchecked("basicFun", 8, 8);
x_231 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_230);
x_232 = lean_mk_string_unchecked("null", 4, 4);
x_233 = l_Lean_Name_mkStr1(x_232);
lean_inc(x_233);
lean_inc(x_223);
x_234 = l_Lean_Syntax_node1(x_223, x_233, x_89);
x_235 = l_Array_mkArray0(lean_box(0));
lean_inc(x_223);
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_223);
lean_ctor_set(x_236, 1, x_233);
lean_ctor_set(x_236, 2, x_235);
x_237 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_223);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_237);
lean_ctor_set(x_75, 0, x_223);
lean_inc(x_223);
x_238 = l_Lean_Syntax_node4(x_223, x_231, x_234, x_236, x_75, x_216);
lean_inc(x_223);
x_239 = l_Lean_Syntax_node2(x_223, x_228, x_229, x_238);
x_240 = l_Lean_Syntax_node2(x_223, x_94, x_226, x_239);
if (lean_is_scalar(x_225)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_225;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_224);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_free_object(x_75);
x_242 = !lean_is_exclusive(x_99);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_99, 0);
x_244 = lean_ctor_get(x_99, 1);
x_245 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_244);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = lean_ctor_get(x_245, 1);
x_249 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_247, x_71, x_248);
lean_dec(x_71);
lean_dec(x_247);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_251 = lean_ctor_get(x_249, 0);
x_252 = lean_mk_string_unchecked("Tactic", 6, 6);
x_253 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_252);
lean_inc(x_91);
lean_inc(x_90);
x_254 = l_Lean_Name_mkStr4(x_90, x_91, x_252, x_253);
x_255 = lean_mk_string_unchecked("null", 4, 4);
x_256 = l_Lean_Name_mkStr1(x_255);
x_257 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_257);
x_258 = l_Lean_Name_mkStr4(x_90, x_91, x_252, x_257);
lean_inc(x_251);
lean_ctor_set_tag(x_245, 2);
lean_ctor_set(x_245, 1, x_257);
lean_ctor_set(x_245, 0, x_251);
lean_inc(x_256);
lean_inc(x_251);
x_259 = l_Lean_Syntax_node1(x_251, x_256, x_89);
lean_inc(x_251);
x_260 = l_Lean_Syntax_node2(x_251, x_258, x_245, x_259);
x_261 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_251);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_261);
lean_ctor_set(x_99, 0, x_251);
lean_inc(x_251);
x_262 = l_Lean_Syntax_node3(x_251, x_256, x_260, x_99, x_243);
x_263 = l_Lean_Syntax_node1(x_251, x_254, x_262);
lean_ctor_set(x_249, 0, x_263);
return x_249;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_264 = lean_ctor_get(x_249, 0);
x_265 = lean_ctor_get(x_249, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_249);
x_266 = lean_mk_string_unchecked("Tactic", 6, 6);
x_267 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_266);
lean_inc(x_91);
lean_inc(x_90);
x_268 = l_Lean_Name_mkStr4(x_90, x_91, x_266, x_267);
x_269 = lean_mk_string_unchecked("null", 4, 4);
x_270 = l_Lean_Name_mkStr1(x_269);
x_271 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_271);
x_272 = l_Lean_Name_mkStr4(x_90, x_91, x_266, x_271);
lean_inc(x_264);
lean_ctor_set_tag(x_245, 2);
lean_ctor_set(x_245, 1, x_271);
lean_ctor_set(x_245, 0, x_264);
lean_inc(x_270);
lean_inc(x_264);
x_273 = l_Lean_Syntax_node1(x_264, x_270, x_89);
lean_inc(x_264);
x_274 = l_Lean_Syntax_node2(x_264, x_272, x_245, x_273);
x_275 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_264);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_275);
lean_ctor_set(x_99, 0, x_264);
lean_inc(x_264);
x_276 = l_Lean_Syntax_node3(x_264, x_270, x_274, x_99, x_243);
x_277 = l_Lean_Syntax_node1(x_264, x_268, x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_265);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_279 = lean_ctor_get(x_245, 0);
x_280 = lean_ctor_get(x_245, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_245);
x_281 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_279, x_71, x_280);
lean_dec(x_71);
lean_dec(x_279);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = lean_mk_string_unchecked("Tactic", 6, 6);
x_286 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_285);
lean_inc(x_91);
lean_inc(x_90);
x_287 = l_Lean_Name_mkStr4(x_90, x_91, x_285, x_286);
x_288 = lean_mk_string_unchecked("null", 4, 4);
x_289 = l_Lean_Name_mkStr1(x_288);
x_290 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_290);
x_291 = l_Lean_Name_mkStr4(x_90, x_91, x_285, x_290);
lean_inc(x_282);
x_292 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_292, 0, x_282);
lean_ctor_set(x_292, 1, x_290);
lean_inc(x_289);
lean_inc(x_282);
x_293 = l_Lean_Syntax_node1(x_282, x_289, x_89);
lean_inc(x_282);
x_294 = l_Lean_Syntax_node2(x_282, x_291, x_292, x_293);
x_295 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_282);
lean_ctor_set_tag(x_99, 2);
lean_ctor_set(x_99, 1, x_295);
lean_ctor_set(x_99, 0, x_282);
lean_inc(x_282);
x_296 = l_Lean_Syntax_node3(x_282, x_289, x_294, x_99, x_243);
x_297 = l_Lean_Syntax_node1(x_282, x_287, x_296);
if (lean_is_scalar(x_284)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_284;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_283);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_299 = lean_ctor_get(x_99, 0);
x_300 = lean_ctor_get(x_99, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_99);
x_301 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_300);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_302, x_71, x_303);
lean_dec(x_71);
lean_dec(x_302);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_308 = x_305;
} else {
 lean_dec_ref(x_305);
 x_308 = lean_box(0);
}
x_309 = lean_mk_string_unchecked("Tactic", 6, 6);
x_310 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_309);
lean_inc(x_91);
lean_inc(x_90);
x_311 = l_Lean_Name_mkStr4(x_90, x_91, x_309, x_310);
x_312 = lean_mk_string_unchecked("null", 4, 4);
x_313 = l_Lean_Name_mkStr1(x_312);
x_314 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_314);
x_315 = l_Lean_Name_mkStr4(x_90, x_91, x_309, x_314);
lean_inc(x_306);
if (lean_is_scalar(x_304)) {
 x_316 = lean_alloc_ctor(2, 2, 0);
} else {
 x_316 = x_304;
 lean_ctor_set_tag(x_316, 2);
}
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_314);
lean_inc(x_313);
lean_inc(x_306);
x_317 = l_Lean_Syntax_node1(x_306, x_313, x_89);
lean_inc(x_306);
x_318 = l_Lean_Syntax_node2(x_306, x_315, x_316, x_317);
x_319 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_306);
x_320 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_320, 0, x_306);
lean_ctor_set(x_320, 1, x_319);
lean_inc(x_306);
x_321 = l_Lean_Syntax_node3(x_306, x_313, x_318, x_320, x_299);
x_322 = l_Lean_Syntax_node1(x_306, x_311, x_321);
if (lean_is_scalar(x_308)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_308;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_307);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_324 = lean_ctor_get(x_79, 0);
x_325 = lean_ctor_get(x_79, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_79);
x_326 = lean_mk_string_unchecked("x", 1, 1);
lean_inc(x_326);
x_327 = l_Lean_Name_mkStr1(x_326);
x_328 = lean_nat_sub(x_4, x_62);
x_329 = l_String_toSubstring_x27(x_326);
x_330 = l_Lean_addMacroScope(x_67, x_327, x_61);
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_332, 0, x_73);
lean_ctor_set(x_332, 1, x_329);
lean_ctor_set(x_332, 2, x_330);
lean_ctor_set(x_332, 3, x_331);
x_333 = lean_mk_string_unchecked("Lean", 4, 4);
x_334 = lean_mk_string_unchecked("Parser", 6, 6);
x_335 = lean_mk_string_unchecked("Term", 4, 4);
x_336 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
x_337 = l_Lean_Name_mkStr4(x_333, x_334, x_335, x_336);
x_338 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_338);
lean_inc(x_324);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_324);
lean_ctor_set(x_339, 1, x_338);
lean_inc(x_332);
lean_inc(x_337);
x_340 = l_Lean_Syntax_node2(x_324, x_337, x_339, x_332);
x_341 = lean_array_push(x_5, x_340);
lean_inc(x_332);
x_342 = lean_array_push(x_6, x_332);
lean_inc(x_71);
x_343 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_328, x_341, x_342, x_71, x_325);
lean_dec(x_328);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_338);
lean_dec(x_337);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
x_347 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_345);
lean_dec(x_71);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
x_351 = l_Lean_SourceInfo_fromRef(x_348, x_3);
lean_dec(x_348);
x_352 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_352);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
x_353 = l_Lean_Name_mkStr4(x_333, x_334, x_335, x_352);
lean_inc(x_351);
if (lean_is_scalar(x_346)) {
 x_354 = lean_alloc_ctor(2, 2, 0);
} else {
 x_354 = x_346;
 lean_ctor_set_tag(x_354, 2);
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_mk_string_unchecked("basicFun", 8, 8);
x_356 = l_Lean_Name_mkStr4(x_333, x_334, x_335, x_355);
x_357 = lean_mk_string_unchecked("null", 4, 4);
x_358 = l_Lean_Name_mkStr1(x_357);
lean_inc(x_358);
lean_inc(x_351);
x_359 = l_Lean_Syntax_node1(x_351, x_358, x_332);
x_360 = l_Array_mkArray0(lean_box(0));
lean_inc(x_351);
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_351);
lean_ctor_set(x_361, 1, x_358);
lean_ctor_set(x_361, 2, x_360);
x_362 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_351);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_362);
lean_ctor_set(x_75, 0, x_351);
lean_inc(x_351);
x_363 = l_Lean_Syntax_node4(x_351, x_356, x_359, x_361, x_75, x_344);
x_364 = l_Lean_Syntax_node2(x_351, x_353, x_354, x_363);
if (lean_is_scalar(x_350)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_350;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_349);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_366 = lean_ctor_get(x_343, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_343, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_368 = x_343;
} else {
 lean_dec_ref(x_343);
 x_368 = lean_box(0);
}
x_369 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_370, x_71, x_371);
lean_dec(x_71);
lean_dec(x_370);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
lean_inc(x_374);
if (lean_is_scalar(x_372)) {
 x_377 = lean_alloc_ctor(2, 2, 0);
} else {
 x_377 = x_372;
 lean_ctor_set_tag(x_377, 2);
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_338);
x_378 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_378);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
x_379 = l_Lean_Name_mkStr4(x_333, x_334, x_335, x_378);
lean_inc(x_374);
if (lean_is_scalar(x_368)) {
 x_380 = lean_alloc_ctor(2, 2, 0);
} else {
 x_380 = x_368;
 lean_ctor_set_tag(x_380, 2);
}
lean_ctor_set(x_380, 0, x_374);
lean_ctor_set(x_380, 1, x_378);
x_381 = lean_mk_string_unchecked("basicFun", 8, 8);
x_382 = l_Lean_Name_mkStr4(x_333, x_334, x_335, x_381);
x_383 = lean_mk_string_unchecked("null", 4, 4);
x_384 = l_Lean_Name_mkStr1(x_383);
lean_inc(x_384);
lean_inc(x_374);
x_385 = l_Lean_Syntax_node1(x_374, x_384, x_332);
x_386 = l_Array_mkArray0(lean_box(0));
lean_inc(x_374);
x_387 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_387, 0, x_374);
lean_ctor_set(x_387, 1, x_384);
lean_ctor_set(x_387, 2, x_386);
x_388 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_374);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_388);
lean_ctor_set(x_75, 0, x_374);
lean_inc(x_374);
x_389 = l_Lean_Syntax_node4(x_374, x_382, x_385, x_387, x_75, x_366);
lean_inc(x_374);
x_390 = l_Lean_Syntax_node2(x_374, x_379, x_380, x_389);
x_391 = l_Lean_Syntax_node2(x_374, x_337, x_377, x_390);
if (lean_is_scalar(x_376)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_376;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_375);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_335);
lean_free_object(x_75);
x_393 = lean_ctor_get(x_343, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_343, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_395 = x_343;
} else {
 lean_dec_ref(x_343);
 x_395 = lean_box(0);
}
x_396 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_394);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
x_400 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_397, x_71, x_398);
lean_dec(x_71);
lean_dec(x_397);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_403 = x_400;
} else {
 lean_dec_ref(x_400);
 x_403 = lean_box(0);
}
x_404 = lean_mk_string_unchecked("Tactic", 6, 6);
x_405 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_404);
lean_inc(x_334);
lean_inc(x_333);
x_406 = l_Lean_Name_mkStr4(x_333, x_334, x_404, x_405);
x_407 = lean_mk_string_unchecked("null", 4, 4);
x_408 = l_Lean_Name_mkStr1(x_407);
x_409 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_409);
x_410 = l_Lean_Name_mkStr4(x_333, x_334, x_404, x_409);
lean_inc(x_401);
if (lean_is_scalar(x_399)) {
 x_411 = lean_alloc_ctor(2, 2, 0);
} else {
 x_411 = x_399;
 lean_ctor_set_tag(x_411, 2);
}
lean_ctor_set(x_411, 0, x_401);
lean_ctor_set(x_411, 1, x_409);
lean_inc(x_408);
lean_inc(x_401);
x_412 = l_Lean_Syntax_node1(x_401, x_408, x_332);
lean_inc(x_401);
x_413 = l_Lean_Syntax_node2(x_401, x_410, x_411, x_412);
x_414 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_401);
if (lean_is_scalar(x_395)) {
 x_415 = lean_alloc_ctor(2, 2, 0);
} else {
 x_415 = x_395;
 lean_ctor_set_tag(x_415, 2);
}
lean_ctor_set(x_415, 0, x_401);
lean_ctor_set(x_415, 1, x_414);
lean_inc(x_401);
x_416 = l_Lean_Syntax_node3(x_401, x_408, x_413, x_415, x_393);
x_417 = l_Lean_Syntax_node1(x_401, x_406, x_416);
if (lean_is_scalar(x_403)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_403;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_402);
return x_418;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_419 = lean_ctor_get(x_75, 0);
x_420 = lean_ctor_get(x_75, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_75);
x_421 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_419, x_71, x_420);
lean_dec(x_419);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_424 = x_421;
} else {
 lean_dec_ref(x_421);
 x_424 = lean_box(0);
}
x_425 = lean_mk_string_unchecked("x", 1, 1);
lean_inc(x_425);
x_426 = l_Lean_Name_mkStr1(x_425);
x_427 = lean_nat_sub(x_4, x_62);
x_428 = l_String_toSubstring_x27(x_425);
x_429 = l_Lean_addMacroScope(x_67, x_426, x_61);
x_430 = lean_box(0);
x_431 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_431, 0, x_73);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_430);
x_432 = lean_mk_string_unchecked("Lean", 4, 4);
x_433 = lean_mk_string_unchecked("Parser", 6, 6);
x_434 = lean_mk_string_unchecked("Term", 4, 4);
x_435 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
x_436 = l_Lean_Name_mkStr4(x_432, x_433, x_434, x_435);
x_437 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_437);
lean_inc(x_422);
if (lean_is_scalar(x_424)) {
 x_438 = lean_alloc_ctor(2, 2, 0);
} else {
 x_438 = x_424;
 lean_ctor_set_tag(x_438, 2);
}
lean_ctor_set(x_438, 0, x_422);
lean_ctor_set(x_438, 1, x_437);
lean_inc(x_431);
lean_inc(x_436);
x_439 = l_Lean_Syntax_node2(x_422, x_436, x_438, x_431);
x_440 = lean_array_push(x_5, x_439);
lean_inc(x_431);
x_441 = lean_array_push(x_6, x_431);
lean_inc(x_71);
x_442 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_427, x_440, x_441, x_71, x_423);
lean_dec(x_427);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_437);
lean_dec(x_436);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_445 = x_442;
} else {
 lean_dec_ref(x_442);
 x_445 = lean_box(0);
}
x_446 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_444);
lean_dec(x_71);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
x_450 = l_Lean_SourceInfo_fromRef(x_447, x_3);
lean_dec(x_447);
x_451 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_451);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
x_452 = l_Lean_Name_mkStr4(x_432, x_433, x_434, x_451);
lean_inc(x_450);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(2, 2, 0);
} else {
 x_453 = x_445;
 lean_ctor_set_tag(x_453, 2);
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
x_454 = lean_mk_string_unchecked("basicFun", 8, 8);
x_455 = l_Lean_Name_mkStr4(x_432, x_433, x_434, x_454);
x_456 = lean_mk_string_unchecked("null", 4, 4);
x_457 = l_Lean_Name_mkStr1(x_456);
lean_inc(x_457);
lean_inc(x_450);
x_458 = l_Lean_Syntax_node1(x_450, x_457, x_431);
x_459 = l_Array_mkArray0(lean_box(0));
lean_inc(x_450);
x_460 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_460, 0, x_450);
lean_ctor_set(x_460, 1, x_457);
lean_ctor_set(x_460, 2, x_459);
x_461 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_450);
x_462 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_462, 0, x_450);
lean_ctor_set(x_462, 1, x_461);
lean_inc(x_450);
x_463 = l_Lean_Syntax_node4(x_450, x_455, x_458, x_460, x_462, x_443);
x_464 = l_Lean_Syntax_node2(x_450, x_452, x_453, x_463);
if (lean_is_scalar(x_449)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_449;
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_448);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_466 = lean_ctor_get(x_442, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_442, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_468 = x_442;
} else {
 lean_dec_ref(x_442);
 x_468 = lean_box(0);
}
x_469 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_467);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_470, x_71, x_471);
lean_dec(x_71);
lean_dec(x_470);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
lean_inc(x_474);
if (lean_is_scalar(x_472)) {
 x_477 = lean_alloc_ctor(2, 2, 0);
} else {
 x_477 = x_472;
 lean_ctor_set_tag(x_477, 2);
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_437);
x_478 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_478);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
x_479 = l_Lean_Name_mkStr4(x_432, x_433, x_434, x_478);
lean_inc(x_474);
if (lean_is_scalar(x_468)) {
 x_480 = lean_alloc_ctor(2, 2, 0);
} else {
 x_480 = x_468;
 lean_ctor_set_tag(x_480, 2);
}
lean_ctor_set(x_480, 0, x_474);
lean_ctor_set(x_480, 1, x_478);
x_481 = lean_mk_string_unchecked("basicFun", 8, 8);
x_482 = l_Lean_Name_mkStr4(x_432, x_433, x_434, x_481);
x_483 = lean_mk_string_unchecked("null", 4, 4);
x_484 = l_Lean_Name_mkStr1(x_483);
lean_inc(x_484);
lean_inc(x_474);
x_485 = l_Lean_Syntax_node1(x_474, x_484, x_431);
x_486 = l_Array_mkArray0(lean_box(0));
lean_inc(x_474);
x_487 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_487, 0, x_474);
lean_ctor_set(x_487, 1, x_484);
lean_ctor_set(x_487, 2, x_486);
x_488 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_474);
x_489 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_489, 0, x_474);
lean_ctor_set(x_489, 1, x_488);
lean_inc(x_474);
x_490 = l_Lean_Syntax_node4(x_474, x_482, x_485, x_487, x_489, x_466);
lean_inc(x_474);
x_491 = l_Lean_Syntax_node2(x_474, x_479, x_480, x_490);
x_492 = l_Lean_Syntax_node2(x_474, x_436, x_477, x_491);
if (lean_is_scalar(x_476)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_476;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_475);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
x_494 = lean_ctor_get(x_442, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_442, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_496 = x_442;
} else {
 lean_dec_ref(x_442);
 x_496 = lean_box(0);
}
x_497 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_71, x_71, x_495);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_500 = x_497;
} else {
 lean_dec_ref(x_497);
 x_500 = lean_box(0);
}
x_501 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_498, x_71, x_499);
lean_dec(x_71);
lean_dec(x_498);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_504 = x_501;
} else {
 lean_dec_ref(x_501);
 x_504 = lean_box(0);
}
x_505 = lean_mk_string_unchecked("Tactic", 6, 6);
x_506 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_505);
lean_inc(x_433);
lean_inc(x_432);
x_507 = l_Lean_Name_mkStr4(x_432, x_433, x_505, x_506);
x_508 = lean_mk_string_unchecked("null", 4, 4);
x_509 = l_Lean_Name_mkStr1(x_508);
x_510 = lean_mk_string_unchecked("intro", 5, 5);
lean_inc(x_510);
x_511 = l_Lean_Name_mkStr4(x_432, x_433, x_505, x_510);
lean_inc(x_502);
if (lean_is_scalar(x_500)) {
 x_512 = lean_alloc_ctor(2, 2, 0);
} else {
 x_512 = x_500;
 lean_ctor_set_tag(x_512, 2);
}
lean_ctor_set(x_512, 0, x_502);
lean_ctor_set(x_512, 1, x_510);
lean_inc(x_509);
lean_inc(x_502);
x_513 = l_Lean_Syntax_node1(x_502, x_509, x_431);
lean_inc(x_502);
x_514 = l_Lean_Syntax_node2(x_502, x_511, x_512, x_513);
x_515 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_502);
if (lean_is_scalar(x_496)) {
 x_516 = lean_alloc_ctor(2, 2, 0);
} else {
 x_516 = x_496;
 lean_ctor_set_tag(x_516, 2);
}
lean_ctor_set(x_516, 0, x_502);
lean_ctor_set(x_516, 1, x_515);
lean_inc(x_502);
x_517 = l_Lean_Syntax_node3(x_502, x_509, x_514, x_516, x_494);
x_518 = l_Lean_Syntax_node1(x_502, x_507, x_517);
if (lean_is_scalar(x_504)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_504;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_503);
return x_519;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(x_1, x_6, x_7, x_8, x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_ctor_get(x_4, 5);
x_11 = l_Lean_replaceRef(x_1, x_10);
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_11);
x_18 = lean_unbox(x_6);
lean_inc(x_9);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_18, x_3, x_7, x_9, x_9, x_17, x_5);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_ctor_get(x_3, 5);
x_11 = l_Lean_replaceRef(x_1, x_10);
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_11);
x_18 = lean_unbox(x_5);
x_19 = lean_unbox(x_6);
lean_inc(x_9);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_18, x_19, x_7, x_9, x_9, x_17, x_4);
lean_dec(x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_mk_string_unchecked("null", 4, 4);
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_box(0);
x_9 = l_Lean_Name_mkStr1(x_5);
x_10 = l_Array_mkArray0(lean_box(0));
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = lean_unbox(x_8);
x_15 = l_Lean_SourceInfo_fromRef(x_7, x_14);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_box(0);
lean_inc(x_4);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_19);
x_21 = lean_mk_string_unchecked("explicit", 8, 8);
x_22 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_21);
x_23 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_15);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
lean_inc(x_15);
x_26 = l_Lean_Syntax_node2(x_15, x_22, x_24, x_25);
x_27 = l_Lean_Syntax_node2(x_15, x_20, x_16, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_3, x_29);
x_31 = lean_array_uset(x_18, x_3, x_27);
x_3 = x_30;
x_4 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_9 = lean_ctor_get(x_5, 5);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
lean_dec(x_9);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Term", 4, 4);
x_16 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Array_mkArray0(lean_box(0));
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_size(x_4);
x_24 = lean_usize_of_nat(x_7);
lean_inc(x_4);
x_25 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(x_5, x_23, x_24, x_4);
x_26 = lean_mk_string_unchecked(",", 1, 1);
x_27 = l_Lean_mkAtom(x_26);
x_28 = l_Lean_mkSepArray(x_25, x_27);
lean_dec(x_25);
x_29 = l_Array_append(lean_box(0), x_21, x_28);
lean_dec(x_28);
lean_inc(x_12);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_12);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_22);
x_33 = l_Lean_Syntax_node6(x_12, x_17, x_18, x_22, x_22, x_30, x_32, x_1);
x_34 = l_Lean_Elab_Term_clearInMatch(x_33, x_4, x_5, x_6);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = l_Lean_Syntax_isNone(x_2);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
x_38 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_35, x_5, x_36);
lean_dec(x_5);
return x_38;
}
else
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_5);
return x_34;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_3, x_39);
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
x_42 = lean_nat_add(x_41, x_39);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_5, 5);
lean_inc(x_49);
lean_dec(x_5);
lean_inc(x_49);
lean_inc(x_41);
lean_inc(x_46);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_50, 5, x_49);
x_51 = l_Lean_SourceInfo_fromRef(x_49, x_8);
lean_dec(x_49);
x_52 = lean_mk_string_unchecked("x", 1, 1);
lean_inc(x_52);
x_53 = l_String_toSubstring_x27(x_52);
x_54 = l_Lean_Name_mkStr1(x_52);
x_55 = l_Lean_addMacroScope(x_46, x_54, x_41);
x_56 = lean_box(0);
lean_inc(x_51);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
lean_inc(x_57);
x_58 = lean_array_push(x_4, x_57);
x_59 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_40, x_58, x_50, x_44);
lean_dec(x_40);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_mk_string_unchecked("Lean", 4, 4);
x_63 = lean_mk_string_unchecked("Parser", 6, 6);
x_64 = lean_mk_string_unchecked("Term", 4, 4);
x_65 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
x_67 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_51);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_69);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_70 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_69);
lean_inc(x_51);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_51);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_mk_string_unchecked("basicFun", 8, 8);
x_73 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_72);
x_74 = lean_mk_string_unchecked("null", 4, 4);
x_75 = l_Lean_Name_mkStr1(x_74);
lean_inc(x_75);
lean_inc(x_51);
x_76 = l_Lean_Syntax_node1(x_51, x_75, x_57);
x_77 = l_Array_mkArray0(lean_box(0));
lean_inc(x_51);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_51);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_51);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_51);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_51);
x_81 = l_Lean_Syntax_node4(x_51, x_73, x_76, x_78, x_80, x_61);
lean_inc(x_51);
x_82 = l_Lean_Syntax_node2(x_51, x_70, x_71, x_81);
x_83 = l_Lean_Syntax_node2(x_51, x_66, x_68, x_82);
lean_ctor_set(x_59, 0, x_83);
return x_59;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_84 = lean_ctor_get(x_59, 0);
x_85 = lean_ctor_get(x_59, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_59);
x_86 = lean_mk_string_unchecked("Lean", 4, 4);
x_87 = lean_mk_string_unchecked("Parser", 6, 6);
x_88 = lean_mk_string_unchecked("Term", 4, 4);
x_89 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
x_90 = l_Lean_Name_mkStr4(x_86, x_87, x_88, x_89);
x_91 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_51);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_51);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_93);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
x_94 = l_Lean_Name_mkStr4(x_86, x_87, x_88, x_93);
lean_inc(x_51);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_51);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_mk_string_unchecked("basicFun", 8, 8);
x_97 = l_Lean_Name_mkStr4(x_86, x_87, x_88, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
lean_inc(x_99);
lean_inc(x_51);
x_100 = l_Lean_Syntax_node1(x_51, x_99, x_57);
x_101 = l_Array_mkArray0(lean_box(0));
lean_inc(x_51);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_51);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
x_103 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_51);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_51);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_51);
x_105 = l_Lean_Syntax_node4(x_51, x_97, x_100, x_102, x_104, x_84);
lean_inc(x_51);
x_106 = l_Lean_Syntax_node2(x_51, x_94, x_95, x_105);
x_107 = l_Lean_Syntax_node2(x_51, x_90, x_92, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_85);
return x_108;
}
}
else
{
lean_dec(x_57);
lean_dec(x_51);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_5);
x_9 = lean_mk_empty_array_with_capacity(x_4);
x_10 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_5, x_7, x_8, x_9, x_2, x_3);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAltsWhereDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Syntax_getArg(x_9, x_10);
lean_dec(x_9);
x_14 = l_Lean_Syntax_getArg(x_13, x_7);
lean_dec(x_13);
x_15 = lean_array_uget(x_4, x_3);
x_16 = l_Lean_Elab_Term_expandSimpleBinderWithType(x_14, x_15, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_4, x_3, x_19);
x_21 = lean_usize_of_nat(x_7);
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_20, x_3, x_17);
x_3 = x_22;
x_4 = x_23;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
lean_inc(x_12);
x_18 = l_Lean_Syntax_isOfKind(x_12, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_1);
x_19 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_12, x_15, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_12, x_21);
x_23 = l_Lean_Syntax_getArg(x_12, x_11);
lean_inc(x_23);
x_24 = l_Lean_Syntax_matchesNull(x_23, x_11);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = l_Lean_Syntax_matchesNull(x_23, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_26 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_12, x_27);
lean_dec(x_12);
x_29 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
lean_inc(x_2);
x_30 = l_Lean_Elab_Term_expandFunBinders(x_29, x_28, x_2, x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_35);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
lean_dec(x_2);
x_46 = l_Lean_SourceInfo_fromRef(x_45, x_24);
lean_dec(x_45);
lean_inc(x_46);
lean_ctor_set_tag(x_32, 2);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 0, x_46);
x_47 = lean_mk_string_unchecked("null", 4, 4);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = l_Array_mkArray0(lean_box(0));
lean_inc(x_49);
x_50 = l_Array_append(lean_box(0), x_49, x_40);
lean_dec(x_40);
lean_inc(x_48);
lean_inc(x_46);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_46);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
x_53 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_46);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_53);
lean_ctor_set(x_31, 0, x_46);
lean_inc(x_46);
x_54 = l_Lean_Syntax_node4(x_46, x_14, x_51, x_52, x_31, x_43);
x_55 = l_Lean_Syntax_node2(x_46, x_8, x_32, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
lean_dec(x_32);
x_57 = lean_ctor_get(x_2, 5);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_SourceInfo_fromRef(x_57, x_24);
lean_dec(x_57);
lean_inc(x_58);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_mk_string_unchecked("null", 4, 4);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = l_Array_mkArray0(lean_box(0));
lean_inc(x_62);
x_63 = l_Array_append(lean_box(0), x_62, x_40);
lean_dec(x_40);
lean_inc(x_61);
lean_inc(x_58);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
lean_inc(x_58);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
x_66 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_58);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_66);
lean_ctor_set(x_31, 0, x_58);
lean_inc(x_58);
x_67 = l_Lean_Syntax_node4(x_58, x_14, x_64, x_65, x_31, x_56);
x_68 = l_Lean_Syntax_node2(x_58, x_8, x_59, x_67);
lean_ctor_set(x_30, 0, x_68);
return x_30;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_69 = lean_ctor_get(x_31, 0);
lean_inc(x_69);
lean_dec(x_31);
x_70 = lean_ctor_get(x_32, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_71 = x_32;
} else {
 lean_dec_ref(x_32);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_2, 5);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_Lean_SourceInfo_fromRef(x_72, x_24);
lean_dec(x_72);
lean_inc(x_73);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(2, 2, 0);
} else {
 x_74 = x_71;
 lean_ctor_set_tag(x_74, 2);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_7);
x_75 = lean_mk_string_unchecked("null", 4, 4);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = l_Array_mkArray0(lean_box(0));
lean_inc(x_77);
x_78 = l_Array_append(lean_box(0), x_77, x_69);
lean_dec(x_69);
lean_inc(x_76);
lean_inc(x_73);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
lean_inc(x_73);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_77);
x_81 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_73);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_73);
x_83 = l_Lean_Syntax_node4(x_73, x_14, x_79, x_80, x_82, x_70);
x_84 = l_Lean_Syntax_node2(x_73, x_8, x_74, x_83);
lean_ctor_set(x_30, 0, x_84);
return x_30;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_85 = lean_ctor_get(x_30, 1);
lean_inc(x_85);
lean_dec(x_30);
x_86 = lean_ctor_get(x_31, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_87 = x_31;
} else {
 lean_dec_ref(x_31);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_32, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_89 = x_32;
} else {
 lean_dec_ref(x_32);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_2, 5);
lean_inc(x_90);
lean_dec(x_2);
x_91 = l_Lean_SourceInfo_fromRef(x_90, x_24);
lean_dec(x_90);
lean_inc(x_91);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(2, 2, 0);
} else {
 x_92 = x_89;
 lean_ctor_set_tag(x_92, 2);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_7);
x_93 = lean_mk_string_unchecked("null", 4, 4);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = l_Array_mkArray0(lean_box(0));
lean_inc(x_95);
x_96 = l_Array_append(lean_box(0), x_95, x_86);
lean_dec(x_86);
lean_inc(x_94);
lean_inc(x_91);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_91);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_95);
x_99 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_91);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(2, 2, 0);
} else {
 x_100 = x_87;
 lean_ctor_set_tag(x_100, 2);
}
lean_ctor_set(x_100, 0, x_91);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_91);
x_101 = l_Lean_Syntax_node4(x_91, x_14, x_97, x_98, x_100, x_88);
x_102 = l_Lean_Syntax_node2(x_91, x_8, x_92, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_85);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_30);
if (x_104 == 0)
{
return x_30;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_30, 0);
x_106 = lean_ctor_get(x_30, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_30);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = l_Lean_Syntax_getArg(x_23, x_21);
lean_dec(x_23);
x_109 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_110 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_109);
x_111 = l_Lean_Syntax_isOfKind(x_108, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_112 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_112;
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; 
x_113 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_114 = lean_array_size(x_113);
x_115 = lean_usize_of_nat(x_21);
x_116 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0(x_1, x_114, x_115, x_113, x_2, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_unsigned_to_nat(3u);
x_120 = l_Lean_Syntax_getArg(x_12, x_119);
lean_dec(x_12);
x_121 = lean_ctor_get(x_2, 5);
lean_inc(x_121);
lean_dec(x_2);
x_122 = lean_box(0);
x_123 = lean_unbox(x_122);
x_124 = l_Lean_SourceInfo_fromRef(x_121, x_123);
lean_dec(x_121);
lean_inc(x_124);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_7);
x_126 = lean_mk_string_unchecked("null", 4, 4);
x_127 = l_Lean_Name_mkStr1(x_126);
x_128 = l_Array_mkArray0(lean_box(0));
lean_inc(x_128);
x_129 = l_Array_append(lean_box(0), x_128, x_118);
lean_dec(x_118);
lean_inc(x_127);
lean_inc(x_124);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
lean_inc(x_124);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
x_132 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_124);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_124);
x_134 = l_Lean_Syntax_node4(x_124, x_14, x_130, x_131, x_133, x_120);
x_135 = l_Lean_Syntax_node2(x_124, x_8, x_125, x_134);
lean_ctor_set(x_116, 0, x_135);
return x_116;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_136 = lean_ctor_get(x_116, 0);
x_137 = lean_ctor_get(x_116, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_116);
x_138 = lean_unsigned_to_nat(3u);
x_139 = l_Lean_Syntax_getArg(x_12, x_138);
lean_dec(x_12);
x_140 = lean_ctor_get(x_2, 5);
lean_inc(x_140);
lean_dec(x_2);
x_141 = lean_box(0);
x_142 = lean_unbox(x_141);
x_143 = l_Lean_SourceInfo_fromRef(x_140, x_142);
lean_dec(x_140);
lean_inc(x_143);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_7);
x_145 = lean_mk_string_unchecked("null", 4, 4);
x_146 = l_Lean_Name_mkStr1(x_145);
x_147 = l_Array_mkArray0(lean_box(0));
lean_inc(x_147);
x_148 = l_Array_append(lean_box(0), x_147, x_136);
lean_dec(x_136);
lean_inc(x_146);
lean_inc(x_143);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_146);
lean_ctor_set(x_149, 2, x_148);
lean_inc(x_143);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_146);
lean_ctor_set(x_150, 2, x_147);
x_151 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_143);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_151);
lean_inc(x_143);
x_153 = l_Lean_Syntax_node4(x_143, x_14, x_149, x_150, x_152, x_139);
x_154 = l_Lean_Syntax_node2(x_143, x_8, x_144, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_137);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_116);
if (x_156 == 0)
{
return x_116;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_116, 0);
x_158 = lean_ctor_get(x_116, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_116);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFun_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandFun", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFun), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandFun", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(596u);
x_8 = lean_unsigned_to_nat(41u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(607u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(45u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(54u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Syntax_getArg(x_12, x_11);
x_18 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_19 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_18);
lean_inc(x_17);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_12);
x_21 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_12, x_17, x_20, x_2, x_3);
lean_dec(x_12);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandExplicitFun(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandExplicitFun", 17, 17);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandExplicitFun___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandExplicitFun", 17, 17);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(609u);
x_8 = lean_unsigned_to_nat(46u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(612u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(50u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(67u);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_Quotation_withNewLocals(lean_box(0), x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Syntax_getId(x_20);
lean_dec(x_20);
x_22 = lean_array_push(x_4, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_22;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_size(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(x_17, x_19, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_4 = x_23;
x_12 = x_24;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_60; uint8_t x_61; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
x_60 = l_Lean_Syntax_getArg(x_18, x_17);
x_61 = l_Lean_Syntax_isNone(x_60);
if (x_61 == 0)
{
uint8_t x_62; 
lean_inc(x_60);
x_62 = l_Lean_Syntax_matchesNull(x_60, x_17);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArg(x_60, x_23);
lean_dec(x_60);
x_65 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_66 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_65);
x_67 = l_Lean_Syntax_isOfKind(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_68;
}
else
{
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
goto block_59;
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
goto block_59;
}
block_59:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_unsigned_to_nat(3u);
x_34 = l_Lean_Syntax_getArg(x_18, x_33);
lean_dec(x_18);
x_35 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders), 4, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_34);
lean_inc(x_30);
x_37 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0(lean_box(0), x_36, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_mk_empty_array_with_capacity(x_23);
x_44 = lean_array_size(x_41);
x_45 = lean_usize_of_nat(x_23);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(x_41, x_44, x_45, x_43, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_40);
lean_dec(x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_49, 0, x_42);
x_50 = l_Lean_Elab_Term_Quotation_withNewLocals(lean_box(0), x_47, x_49, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_48);
lean_dec(x_47);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("precheckFun", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckFun), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_4, x_2, x_2, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_box(1);
x_18 = lean_unbox(x_16);
x_19 = lean_unbox(x_16);
x_20 = lean_unbox(x_17);
x_21 = l_Lean_Meta_mkLambdaFVars(x_3, x_14, x_18, x_2, x_19, x_20, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_21;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("basicFun", 8, 8);
x_20 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_17);
x_25 = l_Lean_Syntax_matchesNull(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_Syntax_getArg(x_18, x_23);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_18, x_28);
lean_dec(x_18);
x_30 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders), 4, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_inc(x_7);
lean_inc(x_3);
x_32 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(x_25);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun___lam__0___boxed), 11, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_elabFunBinders___redArg(x_36, x_2, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_36);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabFun___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabFun", 7, 7);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabFun", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(626u);
x_8 = lean_unsigned_to_nat(35u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(639u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(39u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(46u);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_array_fget(x_19, x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_addLocalVarInfo(x_18, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_14, x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_15);
x_26 = lean_usize_of_nat(x_23);
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_4 = x_25;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg___lam__0), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = l_Array_unzip___redArg(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = lean_box(2);
x_19 = lean_unbox(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_17, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(1);
if (x_3 == 0)
{
lean_object* x_232; 
x_232 = lean_mk_string_unchecked("have", 4, 4);
x_24 = x_4;
x_25 = x_232;
goto block_231;
}
else
{
lean_object* x_233; 
x_233 = lean_mk_string_unchecked("let", 3, 3);
x_24 = x_4;
x_25 = x_233;
goto block_231;
}
block_231:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_mk_string_unchecked("failed to infer '", 17, 17);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_stringToMessageData(x_25);
lean_inc(x_28);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("' declaration type", 18, 18);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_1);
x_33 = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(x_21, x_1, x_32, x_7, x_22);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_mk_string_unchecked("failed to infer universe levels in '", 36, 36);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 0, x_38);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_21);
x_41 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo(x_21, x_1, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (x_24 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_inc(x_21);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_21);
x_46 = lean_box(0);
x_47 = lean_unbox(x_23);
x_48 = lean_unbox(x_23);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_45, x_47, x_48, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(1);
x_53 = lean_unbox(x_23);
x_54 = lean_unbox(x_52);
x_55 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_24, x_53, x_54, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_52);
x_59 = l_Lean_Meta_mkLambdaFVars(x_15, x_50, x_24, x_24, x_24, x_58, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_15);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
if (lean_is_scalar(x_16)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_16;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_14);
lean_ctor_set(x_41, 1, x_62);
lean_ctor_set(x_41, 0, x_56);
lean_ctor_set(x_59, 0, x_41);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
if (lean_is_scalar(x_16)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_16;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_14);
lean_ctor_set(x_41, 1, x_65);
lean_ctor_set(x_41, 0, x_56);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_56);
lean_free_object(x_41);
lean_dec(x_16);
lean_dec(x_14);
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_50);
lean_free_object(x_41);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_71 = !lean_is_exclusive(x_55);
if (x_71 == 0)
{
return x_55;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_55, 0);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_55);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_free_object(x_41);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_75 = !lean_is_exclusive(x_49);
if (x_75 == 0)
{
return x_49;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_49, 0);
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_49);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
lean_dec(x_41);
lean_inc(x_21);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_21);
x_81 = lean_box(0);
x_82 = lean_unbox(x_23);
x_83 = lean_unbox(x_23);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_84 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_80, x_82, x_83, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(1);
x_88 = lean_unbox(x_23);
x_89 = lean_unbox(x_87);
x_90 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_24, x_88, x_89, x_8, x_9, x_10, x_11, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_87);
x_94 = l_Lean_Meta_mkLambdaFVars(x_15, x_85, x_24, x_24, x_24, x_93, x_8, x_9, x_10, x_11, x_92);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_15);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
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
if (lean_is_scalar(x_16)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_16;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_14);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_91);
lean_dec(x_16);
lean_dec(x_14);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_85);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_105 = lean_ctor_get(x_90, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_107 = x_90;
} else {
 lean_dec_ref(x_90);
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
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_109 = lean_ctor_get(x_84, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_84, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_111 = x_84;
} else {
 lean_dec_ref(x_84);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_41);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_41, 1);
x_115 = lean_ctor_get(x_41, 0);
lean_dec(x_115);
x_116 = lean_box(0);
x_117 = lean_box(1);
x_118 = lean_unbox(x_116);
x_119 = lean_unbox(x_23);
x_120 = lean_unbox(x_117);
x_121 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_118, x_119, x_120, x_8, x_9, x_10, x_11, x_114);
lean_dec(x_15);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; uint8_t x_129; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_122);
x_125 = lean_box(0);
x_126 = lean_box(0);
x_127 = lean_unbox(x_125);
x_128 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_124, x_127, x_126, x_8, x_9, x_10, x_11, x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
if (lean_is_scalar(x_16)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_16;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_14);
lean_ctor_set(x_41, 1, x_131);
lean_ctor_set(x_41, 0, x_122);
lean_ctor_set(x_128, 0, x_41);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_128);
if (lean_is_scalar(x_16)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_16;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_14);
lean_ctor_set(x_41, 1, x_134);
lean_ctor_set(x_41, 0, x_122);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_41);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_free_object(x_41);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_136 = !lean_is_exclusive(x_121);
if (x_136 == 0)
{
return x_121;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_121, 0);
x_138 = lean_ctor_get(x_121, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_121);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_41, 1);
lean_inc(x_140);
lean_dec(x_41);
x_141 = lean_box(0);
x_142 = lean_box(1);
x_143 = lean_unbox(x_141);
x_144 = lean_unbox(x_23);
x_145 = lean_unbox(x_142);
x_146 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_143, x_144, x_145, x_8, x_9, x_10, x_11, x_140);
lean_dec(x_15);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_147);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_box(0);
x_151 = lean_box(0);
x_152 = lean_unbox(x_150);
x_153 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_149, x_152, x_151, x_8, x_9, x_10, x_11, x_148);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_16;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_14);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_155);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_160 = lean_ctor_get(x_146, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_146, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_162 = x_146;
} else {
 lean_dec_ref(x_146);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_33, 1);
lean_inc(x_164);
lean_dec(x_33);
x_165 = lean_mk_string_unchecked("failed to infer universe levels in '", 36, 36);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_28);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_31);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_inc(x_21);
x_170 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo(x_21, x_1, x_169, x_6, x_7, x_8, x_9, x_10, x_11, x_164);
if (x_24 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
lean_inc(x_21);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_21);
x_174 = lean_box(0);
x_175 = lean_unbox(x_23);
x_176 = lean_unbox(x_23);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_177 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_173, x_175, x_176, x_174, x_6, x_7, x_8, x_9, x_10, x_11, x_171);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_box(1);
x_181 = lean_unbox(x_23);
x_182 = lean_unbox(x_180);
x_183 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_24, x_181, x_182, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_unbox(x_180);
x_187 = l_Lean_Meta_mkLambdaFVars(x_15, x_178, x_24, x_24, x_24, x_186, x_8, x_9, x_10, x_11, x_185);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_15);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_16;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_14);
if (lean_is_scalar(x_172)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_172;
}
lean_ctor_set(x_192, 0, x_184);
lean_ctor_set(x_192, 1, x_191);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_189);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_184);
lean_dec(x_172);
lean_dec(x_16);
lean_dec(x_14);
x_194 = lean_ctor_get(x_187, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_178);
lean_dec(x_172);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_198 = lean_ctor_get(x_183, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_183, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_200 = x_183;
} else {
 lean_dec_ref(x_183);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_172);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_202 = lean_ctor_get(x_177, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_177, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_204 = x_177;
} else {
 lean_dec_ref(x_177);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; lean_object* x_213; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_206 = lean_ctor_get(x_170, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_207 = x_170;
} else {
 lean_dec_ref(x_170);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
x_209 = lean_box(1);
x_210 = lean_unbox(x_208);
x_211 = lean_unbox(x_23);
x_212 = lean_unbox(x_209);
x_213 = l_Lean_Meta_mkForallFVars(x_15, x_21, x_210, x_211, x_212, x_8, x_9, x_10, x_11, x_206);
lean_dec(x_15);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_214);
x_217 = lean_box(0);
x_218 = lean_box(0);
x_219 = lean_unbox(x_217);
x_220 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_216, x_219, x_218, x_8, x_9, x_10, x_11, x_215);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_16;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_14);
if (lean_is_scalar(x_207)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_207;
}
lean_ctor_set(x_225, 0, x_214);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_222);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_207);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_227 = lean_ctor_get(x_213, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_213, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_229 = x_213;
} else {
 lean_dec_ref(x_213);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_20);
if (x_234 == 0)
{
return x_20;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_20, 0);
x_236 = lean_ctor_get(x_20, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_20);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_5);
lean_inc(x_5);
x_16 = l_Array_toSubarray___redArg(x_5, x_14, x_15);
x_17 = lean_array_size(x_1);
x_18 = lean_usize_of_nat(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0(x_1, x_17, x_18, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_6);
x_22 = lean_box(0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_21, x_3, x_3, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_box(1);
x_28 = lean_unbox(x_26);
x_29 = lean_unbox(x_26);
x_30 = lean_unbox(x_26);
x_31 = lean_unbox(x_27);
x_32 = l_Lean_Meta_mkLambdaFVars(x_5, x_24, x_28, x_29, x_30, x_31, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_35 = l_Lean_Meta_isExprDefEq(x_4, x_33, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_mk_string_unchecked("unexpected error when elaborating 'let'", 39, 39);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_23, 0);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_23);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_19);
if (x_60 == 0)
{
return x_19;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_19, 0);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_19);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_addLocalVarInfo(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_3, x_4, x_4, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_18, x_10, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkLetFun(x_6, x_5, x_21, x_9, x_10, x_11, x_12, x_22);
return x_23;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_addLocalVarInfo(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_3, x_4, x_4, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_18, x_10, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_push(x_24, x_6);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Meta_mkLetFVars(x_25, x_21, x_5, x_27, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_25);
return x_28;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_17;
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(x_7);
x_18 = lean_box(x_8);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed), 12, 4);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Elab_Term_elabBindersEx___redArg(x_2, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_85; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
x_30 = lean_mk_string_unchecked("Elab", 4, 4);
x_31 = lean_mk_string_unchecked("let", 3, 3);
x_32 = lean_mk_string_unchecked("decl", 4, 4);
x_33 = l_Lean_Name_mkStr3(x_30, x_31, x_32);
lean_inc(x_33);
x_34 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_33, x_14, x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_box(x_8);
lean_inc(x_28);
lean_inc(x_29);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed), 13, 4);
lean_closure_set(x_39, 0, x_29);
lean_closure_set(x_39, 1, x_4);
lean_closure_set(x_39, 2, x_38);
lean_closure_set(x_39, 3, x_28);
x_63 = l_Lean_Syntax_getId(x_1);
x_64 = l_Lean_Elab_Term_kindOfBinderName(x_63);
x_85 = lean_unbox(x_35);
lean_dec(x_35);
if (x_85 == 0)
{
lean_dec(x_33);
lean_free_object(x_22);
lean_free_object(x_21);
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = x_15;
x_71 = x_36;
goto block_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_86 = lean_mk_string_unchecked("", 0, 0);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_inc(x_63);
x_88 = l_Lean_MessageData_ofName(x_63);
lean_inc(x_87);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_88);
lean_ctor_set(x_22, 0, x_87);
x_89 = lean_mk_string_unchecked(" : ", 3, 3);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_90);
lean_ctor_set(x_21, 0, x_22);
lean_inc(x_25);
x_91 = l_Lean_MessageData_ofExpr(x_25);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_21);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked(" := ", 4, 4);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_28);
x_96 = l_Lean_MessageData_ofExpr(x_28);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_87);
x_99 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_33, x_98, x_12, x_13, x_14, x_15, x_36);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = x_15;
x_71 = x_100;
goto block_84;
}
block_62:
{
if (x_8 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_25);
if (lean_is_scalar(x_37)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_37;
}
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
lean_dec(x_37);
x_49 = lean_array_get_size(x_29);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_25, x_50, x_39, x_52, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_40);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_40);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
block_84:
{
lean_object* x_72; 
x_72 = lean_box(1);
if (x_7 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed), 13, 5);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_5);
lean_closure_set(x_73, 2, x_6);
lean_closure_set(x_73, 3, x_72);
lean_closure_set(x_73, 4, x_28);
x_74 = lean_box(0);
x_75 = lean_unbox(x_74);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_25);
x_76 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_63, x_75, x_25, x_73, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_40 = x_77;
x_41 = x_65;
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_69;
x_46 = x_70;
x_47 = x_78;
goto block_62;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_25);
return x_76;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_box(x_9);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed), 13, 5);
lean_closure_set(x_80, 0, x_1);
lean_closure_set(x_80, 1, x_5);
lean_closure_set(x_80, 2, x_6);
lean_closure_set(x_80, 3, x_72);
lean_closure_set(x_80, 4, x_79);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_25);
x_81 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_63, x_25, x_28, x_80, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_40 = x_82;
x_41 = x_65;
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_69;
x_46 = x_70;
x_47 = x_83;
goto block_62;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_25);
return x_81;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_157; 
x_101 = lean_ctor_get(x_22, 0);
x_102 = lean_ctor_get(x_22, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_22);
x_103 = lean_mk_string_unchecked("Elab", 4, 4);
x_104 = lean_mk_string_unchecked("let", 3, 3);
x_105 = lean_mk_string_unchecked("decl", 4, 4);
x_106 = l_Lean_Name_mkStr3(x_103, x_104, x_105);
lean_inc(x_106);
x_107 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_14, x_23);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_box(x_8);
lean_inc(x_101);
lean_inc(x_102);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed), 13, 4);
lean_closure_set(x_112, 0, x_102);
lean_closure_set(x_112, 1, x_4);
lean_closure_set(x_112, 2, x_111);
lean_closure_set(x_112, 3, x_101);
x_135 = l_Lean_Syntax_getId(x_1);
x_136 = l_Lean_Elab_Term_kindOfBinderName(x_135);
x_157 = lean_unbox(x_108);
lean_dec(x_108);
if (x_157 == 0)
{
lean_dec(x_106);
lean_free_object(x_21);
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_15;
x_143 = x_109;
goto block_156;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_158 = lean_mk_string_unchecked("", 0, 0);
x_159 = l_Lean_stringToMessageData(x_158);
lean_dec(x_158);
lean_inc(x_135);
x_160 = l_Lean_MessageData_ofName(x_135);
lean_inc(x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_mk_string_unchecked(" : ", 3, 3);
x_163 = l_Lean_stringToMessageData(x_162);
lean_dec(x_162);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_163);
lean_ctor_set(x_21, 0, x_161);
lean_inc(x_25);
x_164 = l_Lean_MessageData_ofExpr(x_25);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_21);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_string_unchecked(" := ", 4, 4);
x_167 = l_Lean_stringToMessageData(x_166);
lean_dec(x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_101);
x_169 = l_Lean_MessageData_ofExpr(x_101);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
x_172 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_171, x_12, x_13, x_14, x_15, x_109);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_15;
x_143 = x_173;
goto block_156;
}
block_134:
{
if (x_8 == 0)
{
lean_object* x_121; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_102);
lean_dec(x_25);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
lean_dec(x_110);
x_122 = lean_array_get_size(x_102);
lean_dec(x_102);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_box(0);
x_125 = lean_unbox(x_124);
x_126 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_25, x_123, x_112, x_125, x_114, x_115, x_116, x_117, x_118, x_119, x_120);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_113);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_113);
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
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
}
block_156:
{
lean_object* x_144; 
x_144 = lean_box(1);
if (x_7 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_145 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed), 13, 5);
lean_closure_set(x_145, 0, x_1);
lean_closure_set(x_145, 1, x_5);
lean_closure_set(x_145, 2, x_6);
lean_closure_set(x_145, 3, x_144);
lean_closure_set(x_145, 4, x_101);
x_146 = lean_box(0);
x_147 = lean_unbox(x_146);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_25);
x_148 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_135, x_147, x_25, x_145, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_113 = x_149;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = x_142;
x_120 = x_150;
goto block_134;
}
else
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_102);
lean_dec(x_25);
return x_148;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_box(x_9);
x_152 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed), 13, 5);
lean_closure_set(x_152, 0, x_1);
lean_closure_set(x_152, 1, x_5);
lean_closure_set(x_152, 2, x_6);
lean_closure_set(x_152, 3, x_144);
lean_closure_set(x_152, 4, x_151);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_25);
x_153 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_135, x_25, x_101, x_152, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_113 = x_154;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = x_142;
x_120 = x_155;
goto block_134;
}
else
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_102);
lean_dec(x_25);
return x_153;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_232; 
x_174 = lean_ctor_get(x_21, 0);
lean_inc(x_174);
lean_dec(x_21);
x_175 = lean_ctor_get(x_22, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_22, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_177 = x_22;
} else {
 lean_dec_ref(x_22);
 x_177 = lean_box(0);
}
x_178 = lean_mk_string_unchecked("Elab", 4, 4);
x_179 = lean_mk_string_unchecked("let", 3, 3);
x_180 = lean_mk_string_unchecked("decl", 4, 4);
x_181 = l_Lean_Name_mkStr3(x_178, x_179, x_180);
lean_inc(x_181);
x_182 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_181, x_14, x_23);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_box(x_8);
lean_inc(x_175);
lean_inc(x_176);
x_187 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed), 13, 4);
lean_closure_set(x_187, 0, x_176);
lean_closure_set(x_187, 1, x_4);
lean_closure_set(x_187, 2, x_186);
lean_closure_set(x_187, 3, x_175);
x_210 = l_Lean_Syntax_getId(x_1);
x_211 = l_Lean_Elab_Term_kindOfBinderName(x_210);
x_232 = lean_unbox(x_183);
lean_dec(x_183);
if (x_232 == 0)
{
lean_dec(x_181);
lean_dec(x_177);
x_212 = x_10;
x_213 = x_11;
x_214 = x_12;
x_215 = x_13;
x_216 = x_14;
x_217 = x_15;
x_218 = x_184;
goto block_231;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_233 = lean_mk_string_unchecked("", 0, 0);
x_234 = l_Lean_stringToMessageData(x_233);
lean_dec(x_233);
lean_inc(x_210);
x_235 = l_Lean_MessageData_ofName(x_210);
lean_inc(x_234);
if (lean_is_scalar(x_177)) {
 x_236 = lean_alloc_ctor(7, 2, 0);
} else {
 x_236 = x_177;
 lean_ctor_set_tag(x_236, 7);
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_mk_string_unchecked(" : ", 3, 3);
x_238 = l_Lean_stringToMessageData(x_237);
lean_dec(x_237);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_238);
lean_inc(x_174);
x_240 = l_Lean_MessageData_ofExpr(x_174);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_mk_string_unchecked(" := ", 4, 4);
x_243 = l_Lean_stringToMessageData(x_242);
lean_dec(x_242);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
lean_inc(x_175);
x_245 = l_Lean_MessageData_ofExpr(x_175);
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_234);
x_248 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_181, x_247, x_12, x_13, x_14, x_15, x_184);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_212 = x_10;
x_213 = x_11;
x_214 = x_12;
x_215 = x_13;
x_216 = x_14;
x_217 = x_15;
x_218 = x_249;
goto block_231;
}
block_209:
{
if (x_8 == 0)
{
lean_object* x_196; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_176);
lean_dec(x_174);
if (lean_is_scalar(x_185)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_185;
}
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
lean_dec(x_185);
x_197 = lean_array_get_size(x_176);
lean_dec(x_176);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_box(0);
x_200 = lean_unbox(x_199);
x_201 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_174, x_198, x_187, x_200, x_189, x_190, x_191, x_192, x_193, x_194, x_195);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_188);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_188);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
block_231:
{
lean_object* x_219; 
x_219 = lean_box(1);
if (x_7 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_220 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed), 13, 5);
lean_closure_set(x_220, 0, x_1);
lean_closure_set(x_220, 1, x_5);
lean_closure_set(x_220, 2, x_6);
lean_closure_set(x_220, 3, x_219);
lean_closure_set(x_220, 4, x_175);
x_221 = lean_box(0);
x_222 = lean_unbox(x_221);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_174);
x_223 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_210, x_222, x_174, x_220, x_211, x_212, x_213, x_214, x_215, x_216, x_217, x_218);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_188 = x_224;
x_189 = x_212;
x_190 = x_213;
x_191 = x_214;
x_192 = x_215;
x_193 = x_216;
x_194 = x_217;
x_195 = x_225;
goto block_209;
}
else
{
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_174);
return x_223;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_box(x_9);
x_227 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed), 13, 5);
lean_closure_set(x_227, 0, x_1);
lean_closure_set(x_227, 1, x_5);
lean_closure_set(x_227, 2, x_6);
lean_closure_set(x_227, 3, x_219);
lean_closure_set(x_227, 4, x_226);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_174);
x_228 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_210, x_174, x_175, x_227, x_211, x_212, x_213, x_214, x_215, x_216, x_217, x_218);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_188 = x_229;
x_189 = x_212;
x_190 = x_213;
x_191 = x_214;
x_192 = x_215;
x_193 = x_216;
x_194 = x_217;
x_195 = x_230;
goto block_209;
}
else
{
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_174);
return x_228;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_20);
if (x_250 == 0)
{
return x_20;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_20, 0);
x_252 = lean_ctor_get(x_20, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_20);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lam__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lam__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lam__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Term_elabLetDeclAux___lam__3(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Elab_Term_expandOptType(x_3, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkLetIdDeclView(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_6, x_2, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_mk_string_unchecked(" := ", 4, 4);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_mkAtomFrom(x_1, x_21, x_23);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_16);
x_28 = lean_array_push(x_27, x_18);
x_29 = lean_array_push(x_28, x_20);
x_30 = lean_array_push(x_29, x_24);
x_31 = lean_array_push(x_30, x_9);
x_32 = lean_box(2);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_mk_string_unchecked("Lean", 4, 4);
x_37 = lean_mk_string_unchecked("Parser", 6, 6);
x_38 = lean_mk_string_unchecked("Term", 4, 4);
x_39 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_40 = l_Lean_Name_mkStr4(x_36, x_37, x_38, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
x_45 = lean_unsigned_to_nat(2u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
x_47 = lean_mk_string_unchecked(" := ", 4, 4);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_mkAtomFrom(x_1, x_47, x_49);
x_51 = lean_unsigned_to_nat(5u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
x_53 = lean_array_push(x_52, x_42);
x_54 = lean_array_push(x_53, x_44);
x_55 = lean_array_push(x_54, x_46);
x_56 = lean_array_push(x_55, x_50);
x_57 = lean_array_push(x_56, x_34);
x_58 = lean_box(2);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_35);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_expandLetEqnsDecl(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_inc(x_16);
x_19 = l_Lean_Syntax_getKind(x_16);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Parser", 6, 6);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_name_eq(x_19, x_24);
lean_dec(x_24);
x_26 = lean_box(1);
if (x_25 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_mk_string_unchecked("letPatDecl", 10, 10);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_39 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_38);
x_40 = lean_name_eq(x_19, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_18);
x_41 = lean_mk_string_unchecked("letEqnsDecl", 11, 11);
x_42 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_41);
x_43 = lean_name_eq(x_19, x_42);
lean_dec(x_42);
lean_dec(x_19);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_44 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_12);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(x_45, 0, x_16);
lean_closure_set(x_45, 1, x_26);
lean_inc(x_10);
lean_inc(x_6);
x_46 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_45, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Syntax_setArg(x_14, x_15, x_47);
lean_inc(x_1);
x_50 = l_Lean_Syntax_setArg(x_1, x_13, x_49);
lean_inc(x_50);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_26);
lean_closure_set(x_51, 3, x_26);
x_52 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_50, x_51, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_14);
if (x_4 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_57 = l_Lean_Syntax_getArg(x_16, x_15);
x_58 = lean_unsigned_to_nat(2u);
x_59 = l_Lean_Syntax_getArg(x_16, x_58);
x_60 = lean_unsigned_to_nat(4u);
x_61 = l_Lean_Syntax_getArg(x_16, x_60);
lean_dec(x_16);
lean_inc(x_57);
x_62 = l_Lean_Syntax_getKind(x_57);
x_63 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_64 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_63);
x_65 = lean_name_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Syntax_isNone(x_59);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_st_ref_get(x_11, x_12);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = l_Lean_Syntax_getArg(x_59, x_15);
lean_dec(x_59);
x_72 = lean_ctor_get(x_10, 5);
lean_inc(x_72);
x_73 = l_Lean_Syntax_getArg(x_71, x_13);
lean_dec(x_71);
x_74 = l_Lean_SourceInfo_fromRef(x_72, x_66);
lean_dec(x_72);
x_75 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_75);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_76 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_75);
lean_inc(x_74);
lean_ctor_set_tag(x_67, 2);
lean_ctor_set(x_67, 1, x_75);
lean_ctor_set(x_67, 0, x_74);
x_77 = lean_mk_string_unchecked("null", 4, 4);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = l_Array_mkArray0(lean_box(0));
lean_inc(x_78);
lean_inc(x_74);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_82 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_81);
x_83 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_84 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_83);
x_85 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_74);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_74);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_78);
lean_inc(x_74);
x_89 = l_Lean_Syntax_node1(x_74, x_78, x_73);
x_90 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_74);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_74);
x_92 = l_Lean_Syntax_node5(x_74, x_84, x_86, x_61, x_88, x_89, x_91);
lean_inc(x_80);
lean_inc(x_74);
x_93 = l_Lean_Syntax_node2(x_74, x_82, x_80, x_92);
lean_inc(x_78);
lean_inc(x_74);
x_94 = l_Lean_Syntax_node1(x_74, x_78, x_93);
x_95 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_74);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_74);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_98 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_97);
x_99 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_100 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_99);
x_101 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_74);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_74);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_78);
lean_inc(x_74);
x_103 = l_Lean_Syntax_node1(x_74, x_78, x_57);
lean_inc(x_78);
lean_inc(x_74);
x_104 = l_Lean_Syntax_node1(x_74, x_78, x_103);
x_105 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_74);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_74);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_74);
x_107 = l_Lean_Syntax_node4(x_74, x_100, x_102, x_104, x_106, x_18);
lean_inc(x_74);
x_108 = l_Lean_Syntax_node1(x_74, x_78, x_107);
lean_inc(x_74);
x_109 = l_Lean_Syntax_node1(x_74, x_98, x_108);
lean_inc(x_80);
x_110 = l_Lean_Syntax_node6(x_74, x_76, x_67, x_80, x_80, x_94, x_96, x_109);
x_27 = x_110;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_69;
goto block_37;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_111 = lean_ctor_get(x_67, 1);
lean_inc(x_111);
lean_dec(x_67);
x_112 = l_Lean_Syntax_getArg(x_59, x_15);
lean_dec(x_59);
x_113 = lean_ctor_get(x_10, 5);
lean_inc(x_113);
x_114 = l_Lean_Syntax_getArg(x_112, x_13);
lean_dec(x_112);
x_115 = l_Lean_SourceInfo_fromRef(x_113, x_66);
lean_dec(x_113);
x_116 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_116);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_117 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_116);
lean_inc(x_115);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_mk_string_unchecked("null", 4, 4);
x_120 = l_Lean_Name_mkStr1(x_119);
x_121 = l_Array_mkArray0(lean_box(0));
lean_inc(x_120);
lean_inc(x_115);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_120);
lean_ctor_set(x_122, 2, x_121);
x_123 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_124 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_123);
x_125 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_126 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_125);
x_127 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_115);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_115);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_115);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_120);
lean_inc(x_115);
x_131 = l_Lean_Syntax_node1(x_115, x_120, x_114);
x_132 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_115);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_115);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_115);
x_134 = l_Lean_Syntax_node5(x_115, x_126, x_128, x_61, x_130, x_131, x_133);
lean_inc(x_122);
lean_inc(x_115);
x_135 = l_Lean_Syntax_node2(x_115, x_124, x_122, x_134);
lean_inc(x_120);
lean_inc(x_115);
x_136 = l_Lean_Syntax_node1(x_115, x_120, x_135);
x_137 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_115);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_115);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_140 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_139);
x_141 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_142 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_141);
x_143 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_115);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_115);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_120);
lean_inc(x_115);
x_145 = l_Lean_Syntax_node1(x_115, x_120, x_57);
lean_inc(x_120);
lean_inc(x_115);
x_146 = l_Lean_Syntax_node1(x_115, x_120, x_145);
x_147 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_115);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_115);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_115);
x_149 = l_Lean_Syntax_node4(x_115, x_142, x_144, x_146, x_148, x_18);
lean_inc(x_115);
x_150 = l_Lean_Syntax_node1(x_115, x_120, x_149);
lean_inc(x_115);
x_151 = l_Lean_Syntax_node1(x_115, x_140, x_150);
lean_inc(x_122);
x_152 = l_Lean_Syntax_node6(x_115, x_117, x_118, x_122, x_122, x_136, x_138, x_151);
x_27 = x_152;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_111;
goto block_37;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
lean_dec(x_59);
x_153 = lean_st_ref_get(x_11, x_12);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_155 = lean_ctor_get(x_153, 1);
x_156 = lean_ctor_get(x_153, 0);
lean_dec(x_156);
x_157 = lean_ctor_get(x_10, 5);
lean_inc(x_157);
x_158 = l_Lean_SourceInfo_fromRef(x_157, x_65);
lean_dec(x_157);
x_159 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_159);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_160 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_159);
lean_inc(x_158);
lean_ctor_set_tag(x_153, 2);
lean_ctor_set(x_153, 1, x_159);
lean_ctor_set(x_153, 0, x_158);
x_161 = lean_mk_string_unchecked("null", 4, 4);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = l_Array_mkArray0(lean_box(0));
lean_inc(x_162);
lean_inc(x_158);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_166 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_165);
lean_inc(x_164);
lean_inc(x_158);
x_167 = l_Lean_Syntax_node2(x_158, x_166, x_164, x_61);
lean_inc(x_162);
lean_inc(x_158);
x_168 = l_Lean_Syntax_node1(x_158, x_162, x_167);
x_169 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_158);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_158);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_172 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_171);
x_173 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_174 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_173);
x_175 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_158);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_158);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_162);
lean_inc(x_158);
x_177 = l_Lean_Syntax_node1(x_158, x_162, x_57);
lean_inc(x_162);
lean_inc(x_158);
x_178 = l_Lean_Syntax_node1(x_158, x_162, x_177);
x_179 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_158);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_158);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_158);
x_181 = l_Lean_Syntax_node4(x_158, x_174, x_176, x_178, x_180, x_18);
lean_inc(x_158);
x_182 = l_Lean_Syntax_node1(x_158, x_162, x_181);
lean_inc(x_158);
x_183 = l_Lean_Syntax_node1(x_158, x_172, x_182);
lean_inc(x_164);
x_184 = l_Lean_Syntax_node6(x_158, x_160, x_153, x_164, x_164, x_168, x_170, x_183);
x_27 = x_184;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_155;
goto block_37;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_185 = lean_ctor_get(x_153, 1);
lean_inc(x_185);
lean_dec(x_153);
x_186 = lean_ctor_get(x_10, 5);
lean_inc(x_186);
x_187 = l_Lean_SourceInfo_fromRef(x_186, x_65);
lean_dec(x_186);
x_188 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_188);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_189 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_188);
lean_inc(x_187);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_mk_string_unchecked("null", 4, 4);
x_192 = l_Lean_Name_mkStr1(x_191);
x_193 = l_Array_mkArray0(lean_box(0));
lean_inc(x_192);
lean_inc(x_187);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_192);
lean_ctor_set(x_194, 2, x_193);
x_195 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_196 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_195);
lean_inc(x_194);
lean_inc(x_187);
x_197 = l_Lean_Syntax_node2(x_187, x_196, x_194, x_61);
lean_inc(x_192);
lean_inc(x_187);
x_198 = l_Lean_Syntax_node1(x_187, x_192, x_197);
x_199 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_187);
x_200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_200, 0, x_187);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_202 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_201);
x_203 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_204 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_203);
x_205 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_187);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_187);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_192);
lean_inc(x_187);
x_207 = l_Lean_Syntax_node1(x_187, x_192, x_57);
lean_inc(x_192);
lean_inc(x_187);
x_208 = l_Lean_Syntax_node1(x_187, x_192, x_207);
x_209 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_187);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_187);
lean_ctor_set(x_210, 1, x_209);
lean_inc(x_187);
x_211 = l_Lean_Syntax_node4(x_187, x_204, x_206, x_208, x_210, x_18);
lean_inc(x_187);
x_212 = l_Lean_Syntax_node1(x_187, x_192, x_211);
lean_inc(x_187);
x_213 = l_Lean_Syntax_node1(x_187, x_202, x_212);
lean_inc(x_194);
x_214 = l_Lean_Syntax_node6(x_187, x_189, x_190, x_194, x_194, x_198, x_200, x_213);
x_27 = x_214;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_185;
goto block_37;
}
}
}
else
{
uint8_t x_215; lean_object* x_216; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_215 = lean_unbox(x_26);
lean_inc(x_11);
x_216 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(x_57, x_215, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_57);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Elab_Term_expandOptType(x_217, x_59);
lean_dec(x_59);
x_220 = lean_mk_empty_array_with_capacity(x_15);
x_221 = l_Lean_Elab_Term_elabLetDeclAux(x_217, x_220, x_219, x_61, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_218);
return x_221;
}
else
{
uint8_t x_222; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_216);
if (x_222 == 0)
{
return x_216;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_216, 0);
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_216);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_mk_string_unchecked("'let_delayed' with patterns is not allowed", 42, 42);
x_227 = l_Lean_stringToMessageData(x_226);
lean_dec(x_226);
x_228 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_227, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
return x_228;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_228, 0);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_228);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_233 = l_Lean_Elab_Term_mkLetIdDeclView(x_16);
lean_dec(x_16);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 3);
lean_inc(x_237);
lean_dec(x_233);
x_238 = l_Lean_Syntax_isIdent(x_234);
if (x_238 == 0)
{
uint8_t x_239; lean_object* x_240; 
x_239 = lean_unbox(x_26);
lean_inc(x_11);
x_240 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(x_234, x_239, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_234);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Elab_Term_elabLetDeclAux(x_241, x_235, x_236, x_237, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_242);
return x_243;
}
else
{
uint8_t x_244; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
return x_240;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_240, 0);
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_240);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
lean_object* x_248; 
x_248 = l_Lean_Elab_Term_elabLetDeclAux(x_234, x_235, x_236, x_237, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_248;
}
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_27);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_35, 0, x_27);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_26);
lean_closure_set(x_35, 3, x_26);
x_36 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_27, x_35, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = lean_unbox(x_11);
x_15 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLetDecl", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLetDecl", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(773u);
x_8 = lean_unsigned_to_nat(27u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(774u);
x_11 = lean_unsigned_to_nat(129u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(31u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(42u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_10);
x_14 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLetFunDecl", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetFunDecl), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLetFunDecl", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(776u);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(777u);
x_11 = lean_unsigned_to_nat(130u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(35u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(49u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_10);
x_14 = lean_unbox(x_11);
x_15 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLetDelayedDecl", 18, 18);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDelayedDecl), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLetDelayedDecl", 18, 18);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(779u);
x_8 = lean_unsigned_to_nat(35u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(780u);
x_11 = lean_unsigned_to_nat(128u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(39u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(57u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = lean_unbox(x_10);
x_15 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("let_tmp", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLetTmpDecl", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetTmpDecl), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLetTmpDecl", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(782u);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(783u);
x_11 = lean_unsigned_to_nat(128u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(35u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(49u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_10744_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("Term", 4, 4);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = lean_mk_string_unchecked("Binders", 7, 7);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(10744u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_5);
lean_inc(x_23);
x_25 = l_Lean_registerTraceClass(x_4, x_24, x_23, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("decl", 4, 4);
lean_inc(x_2);
x_28 = l_Lean_Name_mkStr3(x_2, x_3, x_27);
x_29 = lean_unbox(x_5);
lean_inc(x_23);
x_30 = l_Lean_registerTraceClass(x_28, x_29, x_23, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("autoParam", 9, 9);
x_33 = l_Lean_Name_mkStr2(x_2, x_32);
x_34 = lean_unbox(x_5);
x_35 = l_Lean_registerTraceClass(x_33, x_34, x_23, x_31);
return x_35;
}
else
{
lean_dec(x_23);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
}
lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BindersUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Quotation_Precheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BindersUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2008_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_checkBinderAnnotations = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_checkBinderAnnotations);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandForall__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandForall_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabForall__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabForall_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabArrow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandFun_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabFun_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_10744_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
