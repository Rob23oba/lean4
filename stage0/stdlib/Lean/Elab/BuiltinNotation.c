// Lean compiler output
// Module: Lean.Elab.BuiltinNotation
// Imports: Lean.Compiler.BorrowedAnnotation Lean.Meta.KAbstract Lean.Meta.Closure Lean.Meta.MatchUtil Lean.Compiler.ImplementedByAttr Lean.Elab.SyntheticMVars Lean.Elab.Eval Lean.Elab.Binders
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabShow__1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeAscription__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabRunElab_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f_expandCDotArg_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandParen__1(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0___boxed(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0___boxed(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Term_evalTerm___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed__1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace__1(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_hasCDot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoe_declRange__1(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandShow_declRange__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro__1(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPanic___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwMVarError_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabUnsafe_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHaveI__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandHave__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace_declRange__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeAscription(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoindex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabShow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_debugAssertions;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHaveI_declRange__1(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices_declRange__1(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic__1(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandShow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabShow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandHave_declRange__1(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_List_erase___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab_declRange__1(lean_object*);
lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst_declRange__1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeAscription_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___redArg(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandParen_declRange__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetI_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab_unsafe__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_elabUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT_declRange__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTypeAscription(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hasCDot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoindex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateNameFromImportedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDebugAssert__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry_declRange__1(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTuple__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTypeAscription__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabRunElab_spec__0(size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSuffices(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert__1(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfHasMVars_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTuple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabUnsafe__1(lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetI__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabShow_declRange__1(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_elabPanic___lam__0(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices__1(lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTypeAscription_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTuple_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandAssert(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandShow__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_BuiltinNotation___hyg_8333_(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0(lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation__1(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandHave(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = lean_unbox(x_15);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_elabTerm(x_13, x_14, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_18) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("invalid coercion notation, expected type is not known", 53, 53);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Term_ensureHasType(x_2, x_27, x_29, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
return x_30;
}
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
return x_18;
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCoe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("coeNotation", 11, 11);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("elabCoe", 7, 7);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCoe___boxed), 9, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoe_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabCoe", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(19u);
x_8 = lean_unsigned_to_nat(33u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(25u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = lean_unbox(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_elabTerm(x_10, x_11, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_19 = l_Lean_Meta_coerceToFunction_x3f(x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_mk_string_unchecked("cannot coerce to function", 25, 25);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_indentExpr(x_17);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_39);
x_41 = l_Lean_Meta_coerceToFunction_x3f(x_39, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("cannot coerce to function", 25, 25);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_indentExpr(x_39);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec(x_42);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
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
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCoeFunNotation___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabCoeFunNotation___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeFunNotation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCoeFunNotation(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("coeFunNotation", 14, 14);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("elabCoeFunNotation", 18, 18);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCoeFunNotation___boxed), 9, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabCoeFunNotation", 18, 18);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(27u);
x_8 = lean_unsigned_to_nat(36u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_unsigned_to_nat(56u);
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
x_16 = lean_unsigned_to_nat(58u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = lean_unbox(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_elabTerm(x_10, x_11, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_19 = l_Lean_Meta_coerceToSort_x3f(x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_mk_string_unchecked("cannot coerce to sort", 21, 21);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_indentExpr(x_17);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_39);
x_41 = l_Lean_Meta_coerceToSort_x3f(x_39, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("cannot coerce to sort", 21, 21);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_indentExpr(x_39);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec(x_42);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
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
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCoeSortNotation___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabCoeSortNotation___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCoeSortNotation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCoeSortNotation(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("coeSortNotation", 15, 15);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("elabCoeSortNotation", 19, 19);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCoeSortNotation___boxed), 9, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabCoeSortNotation", 19, 19);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(34u);
x_8 = lean_unsigned_to_nat(37u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(39u);
x_11 = lean_unsigned_to_nat(52u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(41u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(60u);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_17 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_unbox(x_14);
x_20 = l_Lean_MessageData_ofConstName(x_1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_1);
x_32 = l_Lean_Environment_find_x3f(x_29, x_1, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_unbox(x_30);
x_36 = l_Lean_MessageData_ofConstName(x_1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("'", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 6)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MessageData_ofConstName(x_1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("' is not a constructor", 22, 22);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_lt(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_4);
lean_inc(x_5);
x_13 = l_Lean_Meta_getFVarLocalDecl___redArg(x_12, x_5, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_21 = l_Lean_LocalDecl_binderInfo(x_14);
lean_dec(x_14);
x_22 = l_Lean_BinderInfo_isExplicit(x_21);
if (x_22 == 0)
{
x_16 = x_3;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_16 = x_24;
goto block_20;
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_3 = x_16;
x_4 = x_18;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg(x_1, x_2, x_3, x_4, x_9, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg___lam__0), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___redArg(x_1, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, expected type must be an inductive type ", 71, 67);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_array_get_size(x_4);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_2);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg(x_4, x_15, x_3, x_13, x_8, x_10, x_11, x_12);
lean_dec(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("anonymousCtor", 13, 13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_29; 
lean_dec(x_14);
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
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_29;
}
else
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_30 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, expected type must be known", 58, 54);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_37 = lean_whnf(x_36, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_57; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_57 = l_Lean_Expr_getAppFn(x_38);
if (lean_obj_tag(x_57) == 4)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_get(x_8, x_39);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_box(0);
x_65 = lean_unbox(x_64);
x_66 = l_Lean_Environment_find_x3f(x_63, x_58, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_free_object(x_59);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_66, 0);
if (lean_obj_tag(x_70) == 5)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_72, 4);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_free_object(x_70);
lean_dec(x_72);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_unsigned_to_nat(1u);
x_78 = l_Lean_Syntax_getArg(x_1, x_77);
x_79 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_40);
lean_dec(x_38);
x_80 = lean_st_ref_get(x_8, x_62);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Syntax_getArgs(x_78);
lean_dec(x_78);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
lean_inc(x_75);
x_87 = l_Lean_isPrivateNameFromImportedModule(x_86, x_75);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_72);
lean_inc(x_3);
lean_inc(x_75);
x_88 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_89);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_77);
lean_closure_set(x_91, 2, x_84);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_ctor_get(x_92, 2);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_unbox(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_95 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_93, x_91, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Syntax_TSepArray_getElems___redArg(x_85);
lean_dec(x_85);
x_99 = lean_array_get_size(x_98);
x_100 = lean_nat_dec_lt(x_99, x_96);
if (x_100 == 0)
{
uint8_t x_101; 
lean_free_object(x_66);
x_101 = lean_nat_dec_eq(x_99, x_96);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_nat_dec_eq(x_96, x_84);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
lean_free_object(x_80);
lean_free_object(x_73);
lean_free_object(x_70);
lean_free_object(x_59);
x_103 = lean_st_ref_get(x_8, x_97);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_105 = lean_ctor_get(x_103, 1);
x_106 = lean_ctor_get(x_103, 0);
lean_dec(x_106);
x_107 = lean_nat_sub(x_96, x_77);
lean_dec(x_96);
lean_inc(x_107);
lean_inc(x_98);
x_108 = l_Array_toSubarray___redArg(x_98, x_107, x_99);
x_109 = l_Array_ofSubarray___redArg(x_108);
lean_dec(x_108);
x_110 = lean_array_size(x_109);
x_111 = lean_usize_of_nat(x_84);
x_112 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_110, x_111, x_109);
x_113 = l_Lean_mkAtom(x_79);
x_114 = lean_st_ref_get(x_8, x_105);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_116 = lean_ctor_get(x_114, 1);
x_117 = lean_ctor_get(x_114, 0);
lean_dec(x_117);
x_118 = l_Lean_mkSepArray(x_112, x_113);
lean_dec(x_112);
x_119 = lean_ctor_get(x_7, 5);
lean_inc(x_119);
x_120 = lean_mk_string_unchecked("⟨", 3, 1);
x_121 = lean_mk_string_unchecked("null", 4, 4);
x_122 = l_Array_mkArray0(lean_box(0));
lean_inc(x_122);
x_123 = l_Array_append(lean_box(0), x_122, x_118);
lean_dec(x_118);
x_124 = lean_mk_string_unchecked("⟩", 3, 1);
x_125 = l_Lean_SourceInfo_fromRef(x_119, x_102);
lean_dec(x_119);
lean_inc(x_125);
lean_ctor_set_tag(x_114, 2);
lean_ctor_set(x_114, 1, x_120);
lean_ctor_set(x_114, 0, x_125);
x_126 = l_Lean_Name_mkStr1(x_121);
lean_inc(x_126);
lean_inc(x_125);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_123);
lean_inc(x_125);
lean_ctor_set_tag(x_103, 2);
lean_ctor_set(x_103, 1, x_124);
lean_ctor_set(x_103, 0, x_125);
x_128 = l_Array_toSubarray___redArg(x_98, x_84, x_107);
lean_inc(x_125);
x_129 = l_Lean_Syntax_node3(x_125, x_14, x_114, x_127, x_103);
x_130 = l_Array_ofSubarray___redArg(x_128);
lean_dec(x_128);
x_131 = lean_array_push(x_130, x_129);
x_132 = lean_mk_string_unchecked("app", 3, 3);
x_133 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_132);
x_134 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_135 = l_Array_append(lean_box(0), x_122, x_131);
lean_dec(x_131);
lean_inc(x_125);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_126);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Lean_Syntax_node2(x_125, x_133, x_134, x_136);
x_16 = x_137;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_116;
goto block_28;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_138 = lean_ctor_get(x_114, 1);
lean_inc(x_138);
lean_dec(x_114);
x_139 = l_Lean_mkSepArray(x_112, x_113);
lean_dec(x_112);
x_140 = lean_ctor_get(x_7, 5);
lean_inc(x_140);
x_141 = lean_mk_string_unchecked("⟨", 3, 1);
x_142 = lean_mk_string_unchecked("null", 4, 4);
x_143 = l_Array_mkArray0(lean_box(0));
lean_inc(x_143);
x_144 = l_Array_append(lean_box(0), x_143, x_139);
lean_dec(x_139);
x_145 = lean_mk_string_unchecked("⟩", 3, 1);
x_146 = l_Lean_SourceInfo_fromRef(x_140, x_102);
lean_dec(x_140);
lean_inc(x_146);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = l_Lean_Name_mkStr1(x_142);
lean_inc(x_148);
lean_inc(x_146);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_144);
lean_inc(x_146);
lean_ctor_set_tag(x_103, 2);
lean_ctor_set(x_103, 1, x_145);
lean_ctor_set(x_103, 0, x_146);
x_150 = l_Array_toSubarray___redArg(x_98, x_84, x_107);
lean_inc(x_146);
x_151 = l_Lean_Syntax_node3(x_146, x_14, x_147, x_149, x_103);
x_152 = l_Array_ofSubarray___redArg(x_150);
lean_dec(x_150);
x_153 = lean_array_push(x_152, x_151);
x_154 = lean_mk_string_unchecked("app", 3, 3);
x_155 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_154);
x_156 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_157 = l_Array_append(lean_box(0), x_143, x_153);
lean_dec(x_153);
lean_inc(x_146);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_146);
lean_ctor_set(x_158, 1, x_148);
lean_ctor_set(x_158, 2, x_157);
x_159 = l_Lean_Syntax_node2(x_146, x_155, x_156, x_158);
x_16 = x_159;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_138;
goto block_28;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_160 = lean_ctor_get(x_103, 1);
lean_inc(x_160);
lean_dec(x_103);
x_161 = lean_nat_sub(x_96, x_77);
lean_dec(x_96);
lean_inc(x_161);
lean_inc(x_98);
x_162 = l_Array_toSubarray___redArg(x_98, x_161, x_99);
x_163 = l_Array_ofSubarray___redArg(x_162);
lean_dec(x_162);
x_164 = lean_array_size(x_163);
x_165 = lean_usize_of_nat(x_84);
x_166 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_164, x_165, x_163);
x_167 = l_Lean_mkAtom(x_79);
x_168 = lean_st_ref_get(x_8, x_160);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = l_Lean_mkSepArray(x_166, x_167);
lean_dec(x_166);
x_172 = lean_ctor_get(x_7, 5);
lean_inc(x_172);
x_173 = lean_mk_string_unchecked("⟨", 3, 1);
x_174 = lean_mk_string_unchecked("null", 4, 4);
x_175 = l_Array_mkArray0(lean_box(0));
lean_inc(x_175);
x_176 = l_Array_append(lean_box(0), x_175, x_171);
lean_dec(x_171);
x_177 = lean_mk_string_unchecked("⟩", 3, 1);
x_178 = l_Lean_SourceInfo_fromRef(x_172, x_102);
lean_dec(x_172);
lean_inc(x_178);
if (lean_is_scalar(x_170)) {
 x_179 = lean_alloc_ctor(2, 2, 0);
} else {
 x_179 = x_170;
 lean_ctor_set_tag(x_179, 2);
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_173);
x_180 = l_Lean_Name_mkStr1(x_174);
lean_inc(x_180);
lean_inc(x_178);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_176);
lean_inc(x_178);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_177);
x_183 = l_Array_toSubarray___redArg(x_98, x_84, x_161);
lean_inc(x_178);
x_184 = l_Lean_Syntax_node3(x_178, x_14, x_179, x_181, x_182);
x_185 = l_Array_ofSubarray___redArg(x_183);
lean_dec(x_183);
x_186 = lean_array_push(x_185, x_184);
x_187 = lean_mk_string_unchecked("app", 3, 3);
x_188 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_187);
x_189 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_190 = l_Array_append(lean_box(0), x_175, x_186);
lean_dec(x_186);
lean_inc(x_178);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_178);
lean_ctor_set(x_191, 1, x_180);
lean_ctor_set(x_191, 2, x_190);
x_192 = l_Lean_Syntax_node2(x_178, x_188, x_189, x_191);
x_16 = x_192;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_169;
goto block_28;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_79);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
x_195 = l_Lean_MessageData_ofName(x_75);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_195);
lean_ctor_set(x_80, 0, x_194);
x_196 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_197);
lean_ctor_set(x_73, 0, x_80);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_99);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_198);
x_199 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_199);
lean_ctor_set(x_59, 0, x_73);
x_200 = lean_mk_string_unchecked(" provided", 9, 9);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_59);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_202, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_203);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_99);
lean_dec(x_96);
lean_free_object(x_80);
lean_dec(x_79);
lean_free_object(x_73);
lean_free_object(x_70);
lean_free_object(x_59);
lean_dec(x_14);
x_208 = lean_st_ref_get(x_8, x_97);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_7, 5);
lean_inc(x_210);
x_211 = lean_unbox(x_64);
x_212 = l_Lean_SourceInfo_fromRef(x_210, x_211);
lean_dec(x_210);
x_213 = lean_mk_string_unchecked("app", 3, 3);
x_214 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_213);
x_215 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_216 = lean_mk_string_unchecked("null", 4, 4);
x_217 = l_Lean_Name_mkStr1(x_216);
x_218 = l_Array_mkArray0(lean_box(0));
x_219 = l_Array_append(lean_box(0), x_218, x_98);
lean_dec(x_98);
lean_inc(x_212);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_212);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = l_Lean_Syntax_node2(x_212, x_214, x_215, x_220);
x_16 = x_221;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_209;
goto block_28;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_dec(x_98);
lean_dec(x_79);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_222 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_223 = l_Lean_stringToMessageData(x_222);
lean_dec(x_222);
x_224 = l_Lean_MessageData_ofName(x_75);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_224);
lean_ctor_set(x_80, 0, x_223);
x_225 = lean_mk_string_unchecked("' has #", 7, 7);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_226);
lean_ctor_set(x_73, 0, x_80);
x_227 = l___private_Init_Data_Repr_0__Nat_reprFast(x_96);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_227);
x_228 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_228);
lean_ctor_set(x_59, 0, x_73);
x_229 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_230 = l_Lean_stringToMessageData(x_229);
lean_dec(x_229);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_59);
lean_ctor_set(x_231, 1, x_230);
x_232 = l___private_Init_Data_Repr_0__Nat_reprFast(x_99);
lean_ctor_set_tag(x_66, 3);
lean_ctor_set(x_66, 0, x_232);
x_233 = l_Lean_MessageData_ofFormat(x_66);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_mk_string_unchecked(" provided", 9, 9);
x_236 = l_Lean_stringToMessageData(x_235);
lean_dec(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_237, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
return x_238;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_238);
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
lean_dec(x_85);
lean_free_object(x_80);
lean_dec(x_79);
lean_free_object(x_73);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_243 = !lean_is_exclusive(x_95);
if (x_243 == 0)
{
return x_95;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_95, 0);
x_245 = lean_ctor_get(x_95, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_95);
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
lean_dec(x_85);
lean_free_object(x_80);
lean_dec(x_79);
lean_free_object(x_73);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_247 = !lean_is_exclusive(x_88);
if (x_247 == 0)
{
return x_88;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_88, 0);
x_249 = lean_ctor_get(x_88, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_88);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
x_253 = lean_ctor_get(x_72, 0);
lean_inc(x_253);
lean_dec(x_72);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec(x_253);
x_255 = l_Lean_MessageData_ofName(x_254);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_255);
lean_ctor_set(x_80, 0, x_252);
x_256 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_257 = l_Lean_stringToMessageData(x_256);
lean_dec(x_256);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_257);
lean_ctor_set(x_73, 0, x_80);
x_258 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
return x_258;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_258);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_263 = lean_ctor_get(x_80, 0);
x_264 = lean_ctor_get(x_80, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_80);
x_265 = lean_unsigned_to_nat(0u);
x_266 = l_Lean_Syntax_getArgs(x_78);
lean_dec(x_78);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
lean_dec(x_263);
lean_inc(x_75);
x_268 = l_Lean_isPrivateNameFromImportedModule(x_267, x_75);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec(x_72);
lean_inc(x_3);
lean_inc(x_75);
x_269 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_264);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_270);
x_272 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_272, 0, x_270);
lean_closure_set(x_272, 1, x_77);
lean_closure_set(x_272, 2, x_265);
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_ctor_get(x_273, 2);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_unbox(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_276 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_274, x_272, x_275, x_3, x_4, x_5, x_6, x_7, x_8, x_271);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Lean_Syntax_TSepArray_getElems___redArg(x_266);
lean_dec(x_266);
x_280 = lean_array_get_size(x_279);
x_281 = lean_nat_dec_lt(x_280, x_277);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_66);
x_282 = lean_nat_dec_eq(x_280, x_277);
if (x_282 == 0)
{
uint8_t x_283; 
x_283 = lean_nat_dec_eq(x_277, x_265);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; size_t x_290; size_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_free_object(x_73);
lean_free_object(x_70);
lean_free_object(x_59);
x_284 = lean_st_ref_get(x_8, x_278);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = lean_nat_sub(x_277, x_77);
lean_dec(x_277);
lean_inc(x_287);
lean_inc(x_279);
x_288 = l_Array_toSubarray___redArg(x_279, x_287, x_280);
x_289 = l_Array_ofSubarray___redArg(x_288);
lean_dec(x_288);
x_290 = lean_array_size(x_289);
x_291 = lean_usize_of_nat(x_265);
x_292 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_290, x_291, x_289);
x_293 = l_Lean_mkAtom(x_79);
x_294 = lean_st_ref_get(x_8, x_285);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
x_297 = l_Lean_mkSepArray(x_292, x_293);
lean_dec(x_292);
x_298 = lean_ctor_get(x_7, 5);
lean_inc(x_298);
x_299 = lean_mk_string_unchecked("⟨", 3, 1);
x_300 = lean_mk_string_unchecked("null", 4, 4);
x_301 = l_Array_mkArray0(lean_box(0));
lean_inc(x_301);
x_302 = l_Array_append(lean_box(0), x_301, x_297);
lean_dec(x_297);
x_303 = lean_mk_string_unchecked("⟩", 3, 1);
x_304 = l_Lean_SourceInfo_fromRef(x_298, x_283);
lean_dec(x_298);
lean_inc(x_304);
if (lean_is_scalar(x_296)) {
 x_305 = lean_alloc_ctor(2, 2, 0);
} else {
 x_305 = x_296;
 lean_ctor_set_tag(x_305, 2);
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_299);
x_306 = l_Lean_Name_mkStr1(x_300);
lean_inc(x_306);
lean_inc(x_304);
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set(x_307, 2, x_302);
lean_inc(x_304);
if (lean_is_scalar(x_286)) {
 x_308 = lean_alloc_ctor(2, 2, 0);
} else {
 x_308 = x_286;
 lean_ctor_set_tag(x_308, 2);
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_303);
x_309 = l_Array_toSubarray___redArg(x_279, x_265, x_287);
lean_inc(x_304);
x_310 = l_Lean_Syntax_node3(x_304, x_14, x_305, x_307, x_308);
x_311 = l_Array_ofSubarray___redArg(x_309);
lean_dec(x_309);
x_312 = lean_array_push(x_311, x_310);
x_313 = lean_mk_string_unchecked("app", 3, 3);
x_314 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_313);
x_315 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_316 = l_Array_append(lean_box(0), x_301, x_312);
lean_dec(x_312);
lean_inc(x_304);
x_317 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_317, 0, x_304);
lean_ctor_set(x_317, 1, x_306);
lean_ctor_set(x_317, 2, x_316);
x_318 = l_Lean_Syntax_node2(x_304, x_314, x_315, x_317);
x_16 = x_318;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_295;
goto block_28;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_79);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_319 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
x_321 = l_Lean_MessageData_ofName(x_75);
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_324 = l_Lean_stringToMessageData(x_323);
lean_dec(x_323);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_324);
lean_ctor_set(x_73, 0, x_322);
x_325 = l___private_Init_Data_Repr_0__Nat_reprFast(x_280);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_325);
x_326 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_326);
lean_ctor_set(x_59, 0, x_73);
x_327 = lean_mk_string_unchecked(" provided", 9, 9);
x_328 = l_Lean_stringToMessageData(x_327);
lean_dec(x_327);
x_329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_329, 0, x_59);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_329, x_3, x_4, x_5, x_6, x_7, x_8, x_278);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_79);
lean_free_object(x_73);
lean_free_object(x_70);
lean_free_object(x_59);
lean_dec(x_14);
x_335 = lean_st_ref_get(x_8, x_278);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_337 = lean_ctor_get(x_7, 5);
lean_inc(x_337);
x_338 = lean_unbox(x_64);
x_339 = l_Lean_SourceInfo_fromRef(x_337, x_338);
lean_dec(x_337);
x_340 = lean_mk_string_unchecked("app", 3, 3);
x_341 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_340);
x_342 = l_Lean_mkCIdentFrom(x_1, x_75, x_15);
x_343 = lean_mk_string_unchecked("null", 4, 4);
x_344 = l_Lean_Name_mkStr1(x_343);
x_345 = l_Array_mkArray0(lean_box(0));
x_346 = l_Array_append(lean_box(0), x_345, x_279);
lean_dec(x_279);
lean_inc(x_339);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_339);
lean_ctor_set(x_347, 1, x_344);
lean_ctor_set(x_347, 2, x_346);
x_348 = l_Lean_Syntax_node2(x_339, x_341, x_342, x_347);
x_16 = x_348;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_336;
goto block_28;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_279);
lean_dec(x_79);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_349 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_350 = l_Lean_stringToMessageData(x_349);
lean_dec(x_349);
x_351 = l_Lean_MessageData_ofName(x_75);
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_mk_string_unchecked("' has #", 7, 7);
x_354 = l_Lean_stringToMessageData(x_353);
lean_dec(x_353);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_354);
lean_ctor_set(x_73, 0, x_352);
x_355 = l___private_Init_Data_Repr_0__Nat_reprFast(x_277);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_355);
x_356 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_356);
lean_ctor_set(x_59, 0, x_73);
x_357 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_358 = l_Lean_stringToMessageData(x_357);
lean_dec(x_357);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_59);
lean_ctor_set(x_359, 1, x_358);
x_360 = l___private_Init_Data_Repr_0__Nat_reprFast(x_280);
lean_ctor_set_tag(x_66, 3);
lean_ctor_set(x_66, 0, x_360);
x_361 = l_Lean_MessageData_ofFormat(x_66);
x_362 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_mk_string_unchecked(" provided", 9, 9);
x_364 = l_Lean_stringToMessageData(x_363);
lean_dec(x_363);
x_365 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_365, x_3, x_4, x_5, x_6, x_7, x_8, x_278);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_266);
lean_dec(x_79);
lean_free_object(x_73);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_371 = lean_ctor_get(x_276, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_276, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_373 = x_276;
} else {
 lean_dec_ref(x_276);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_266);
lean_dec(x_79);
lean_free_object(x_73);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_375 = lean_ctor_get(x_269, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_269, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_377 = x_269;
} else {
 lean_dec_ref(x_269);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_266);
lean_dec(x_79);
lean_dec(x_75);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_379 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_380 = l_Lean_stringToMessageData(x_379);
lean_dec(x_379);
x_381 = lean_ctor_get(x_72, 0);
lean_inc(x_381);
lean_dec(x_72);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec(x_381);
x_383 = l_Lean_MessageData_ofName(x_382);
x_384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_386 = l_Lean_stringToMessageData(x_385);
lean_dec(x_385);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_386);
lean_ctor_set(x_73, 0, x_384);
x_387 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_264);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
else
{
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_73);
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_70);
lean_dec(x_72);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_392 = lean_ctor_get(x_73, 0);
x_393 = lean_ctor_get(x_73, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_73);
x_394 = lean_unsigned_to_nat(1u);
x_395 = l_Lean_Syntax_getArg(x_1, x_394);
x_396 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
lean_dec(x_40);
lean_dec(x_38);
x_397 = lean_st_ref_get(x_8, x_62);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
x_401 = lean_unsigned_to_nat(0u);
x_402 = l_Lean_Syntax_getArgs(x_395);
lean_dec(x_395);
x_403 = lean_ctor_get(x_398, 0);
lean_inc(x_403);
lean_dec(x_398);
lean_inc(x_392);
x_404 = l_Lean_isPrivateNameFromImportedModule(x_403, x_392);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; 
lean_dec(x_72);
lean_inc(x_3);
lean_inc(x_392);
x_405 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_392, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_406);
x_408 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_408, 0, x_406);
lean_closure_set(x_408, 1, x_394);
lean_closure_set(x_408, 2, x_401);
x_409 = lean_ctor_get(x_406, 0);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_ctor_get(x_409, 2);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_unbox(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_412 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_410, x_408, x_411, x_3, x_4, x_5, x_6, x_7, x_8, x_407);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = l_Lean_Syntax_TSepArray_getElems___redArg(x_402);
lean_dec(x_402);
x_416 = lean_array_get_size(x_415);
x_417 = lean_nat_dec_lt(x_416, x_413);
if (x_417 == 0)
{
uint8_t x_418; 
lean_free_object(x_66);
x_418 = lean_nat_dec_eq(x_416, x_413);
if (x_418 == 0)
{
uint8_t x_419; 
x_419 = lean_nat_dec_eq(x_413, x_401);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; size_t x_426; size_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_400);
lean_free_object(x_70);
lean_free_object(x_59);
x_420 = lean_st_ref_get(x_8, x_414);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_422 = x_420;
} else {
 lean_dec_ref(x_420);
 x_422 = lean_box(0);
}
x_423 = lean_nat_sub(x_413, x_394);
lean_dec(x_413);
lean_inc(x_423);
lean_inc(x_415);
x_424 = l_Array_toSubarray___redArg(x_415, x_423, x_416);
x_425 = l_Array_ofSubarray___redArg(x_424);
lean_dec(x_424);
x_426 = lean_array_size(x_425);
x_427 = lean_usize_of_nat(x_401);
x_428 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_426, x_427, x_425);
x_429 = l_Lean_mkAtom(x_396);
x_430 = lean_st_ref_get(x_8, x_421);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
x_433 = l_Lean_mkSepArray(x_428, x_429);
lean_dec(x_428);
x_434 = lean_ctor_get(x_7, 5);
lean_inc(x_434);
x_435 = lean_mk_string_unchecked("⟨", 3, 1);
x_436 = lean_mk_string_unchecked("null", 4, 4);
x_437 = l_Array_mkArray0(lean_box(0));
lean_inc(x_437);
x_438 = l_Array_append(lean_box(0), x_437, x_433);
lean_dec(x_433);
x_439 = lean_mk_string_unchecked("⟩", 3, 1);
x_440 = l_Lean_SourceInfo_fromRef(x_434, x_419);
lean_dec(x_434);
lean_inc(x_440);
if (lean_is_scalar(x_432)) {
 x_441 = lean_alloc_ctor(2, 2, 0);
} else {
 x_441 = x_432;
 lean_ctor_set_tag(x_441, 2);
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_435);
x_442 = l_Lean_Name_mkStr1(x_436);
lean_inc(x_442);
lean_inc(x_440);
x_443 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set(x_443, 2, x_438);
lean_inc(x_440);
if (lean_is_scalar(x_422)) {
 x_444 = lean_alloc_ctor(2, 2, 0);
} else {
 x_444 = x_422;
 lean_ctor_set_tag(x_444, 2);
}
lean_ctor_set(x_444, 0, x_440);
lean_ctor_set(x_444, 1, x_439);
x_445 = l_Array_toSubarray___redArg(x_415, x_401, x_423);
lean_inc(x_440);
x_446 = l_Lean_Syntax_node3(x_440, x_14, x_441, x_443, x_444);
x_447 = l_Array_ofSubarray___redArg(x_445);
lean_dec(x_445);
x_448 = lean_array_push(x_447, x_446);
x_449 = lean_mk_string_unchecked("app", 3, 3);
x_450 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_449);
x_451 = l_Lean_mkCIdentFrom(x_1, x_392, x_15);
x_452 = l_Array_append(lean_box(0), x_437, x_448);
lean_dec(x_448);
lean_inc(x_440);
x_453 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_453, 0, x_440);
lean_ctor_set(x_453, 1, x_442);
lean_ctor_set(x_453, 2, x_452);
x_454 = l_Lean_Syntax_node2(x_440, x_450, x_451, x_453);
x_16 = x_454;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_431;
goto block_28;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_415);
lean_dec(x_413);
lean_dec(x_396);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_455 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_456 = l_Lean_stringToMessageData(x_455);
lean_dec(x_455);
x_457 = l_Lean_MessageData_ofName(x_392);
if (lean_is_scalar(x_400)) {
 x_458 = lean_alloc_ctor(7, 2, 0);
} else {
 x_458 = x_400;
 lean_ctor_set_tag(x_458, 7);
}
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_460 = l_Lean_stringToMessageData(x_459);
lean_dec(x_459);
x_461 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_460);
x_462 = l___private_Init_Data_Repr_0__Nat_reprFast(x_416);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_462);
x_463 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_463);
lean_ctor_set(x_59, 0, x_461);
x_464 = lean_mk_string_unchecked(" provided", 9, 9);
x_465 = l_Lean_stringToMessageData(x_464);
lean_dec(x_464);
x_466 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_466, 0, x_59);
lean_ctor_set(x_466, 1, x_465);
x_467 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_466, x_3, x_4, x_5, x_6, x_7, x_8, x_414);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_416);
lean_dec(x_413);
lean_dec(x_400);
lean_dec(x_396);
lean_free_object(x_70);
lean_free_object(x_59);
lean_dec(x_14);
x_472 = lean_st_ref_get(x_8, x_414);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_474 = lean_ctor_get(x_7, 5);
lean_inc(x_474);
x_475 = lean_unbox(x_64);
x_476 = l_Lean_SourceInfo_fromRef(x_474, x_475);
lean_dec(x_474);
x_477 = lean_mk_string_unchecked("app", 3, 3);
x_478 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_477);
x_479 = l_Lean_mkCIdentFrom(x_1, x_392, x_15);
x_480 = lean_mk_string_unchecked("null", 4, 4);
x_481 = l_Lean_Name_mkStr1(x_480);
x_482 = l_Array_mkArray0(lean_box(0));
x_483 = l_Array_append(lean_box(0), x_482, x_415);
lean_dec(x_415);
lean_inc(x_476);
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_476);
lean_ctor_set(x_484, 1, x_481);
lean_ctor_set(x_484, 2, x_483);
x_485 = l_Lean_Syntax_node2(x_476, x_478, x_479, x_484);
x_16 = x_485;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_473;
goto block_28;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_415);
lean_dec(x_396);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_487 = l_Lean_stringToMessageData(x_486);
lean_dec(x_486);
x_488 = l_Lean_MessageData_ofName(x_392);
if (lean_is_scalar(x_400)) {
 x_489 = lean_alloc_ctor(7, 2, 0);
} else {
 x_489 = x_400;
 lean_ctor_set_tag(x_489, 7);
}
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_mk_string_unchecked("' has #", 7, 7);
x_491 = l_Lean_stringToMessageData(x_490);
lean_dec(x_490);
x_492 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_491);
x_493 = l___private_Init_Data_Repr_0__Nat_reprFast(x_413);
lean_ctor_set_tag(x_70, 3);
lean_ctor_set(x_70, 0, x_493);
x_494 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_494);
lean_ctor_set(x_59, 0, x_492);
x_495 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_496 = l_Lean_stringToMessageData(x_495);
lean_dec(x_495);
x_497 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_497, 0, x_59);
lean_ctor_set(x_497, 1, x_496);
x_498 = l___private_Init_Data_Repr_0__Nat_reprFast(x_416);
lean_ctor_set_tag(x_66, 3);
lean_ctor_set(x_66, 0, x_498);
x_499 = l_Lean_MessageData_ofFormat(x_66);
x_500 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_mk_string_unchecked(" provided", 9, 9);
x_502 = l_Lean_stringToMessageData(x_501);
lean_dec(x_501);
x_503 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_502);
x_504 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_503, x_3, x_4, x_5, x_6, x_7, x_8, x_414);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_507 = x_504;
} else {
 lean_dec_ref(x_504);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_402);
lean_dec(x_400);
lean_dec(x_396);
lean_dec(x_392);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_509 = lean_ctor_get(x_412, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_412, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_511 = x_412;
} else {
 lean_dec_ref(x_412);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_510);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_402);
lean_dec(x_400);
lean_dec(x_396);
lean_dec(x_392);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_513 = lean_ctor_get(x_405, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_405, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_515 = x_405;
} else {
 lean_dec_ref(x_405);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_402);
lean_dec(x_396);
lean_dec(x_392);
lean_free_object(x_70);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_517 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_518 = l_Lean_stringToMessageData(x_517);
lean_dec(x_517);
x_519 = lean_ctor_get(x_72, 0);
lean_inc(x_519);
lean_dec(x_72);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
lean_dec(x_519);
x_521 = l_Lean_MessageData_ofName(x_520);
if (lean_is_scalar(x_400)) {
 x_522 = lean_alloc_ctor(7, 2, 0);
} else {
 x_522 = x_400;
 lean_ctor_set_tag(x_522, 7);
}
lean_ctor_set(x_522, 0, x_518);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_524 = l_Lean_stringToMessageData(x_523);
lean_dec(x_523);
x_525 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_524);
x_526 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_525, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_392);
lean_free_object(x_70);
lean_dec(x_72);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
}
}
}
else
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_70, 0);
lean_inc(x_531);
lean_dec(x_70);
x_532 = lean_ctor_get(x_531, 4);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_dec(x_531);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = lean_unsigned_to_nat(1u);
x_537 = l_Lean_Syntax_getArg(x_1, x_536);
x_538 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
lean_dec(x_40);
lean_dec(x_38);
x_539 = lean_st_ref_get(x_8, x_62);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
x_543 = lean_unsigned_to_nat(0u);
x_544 = l_Lean_Syntax_getArgs(x_537);
lean_dec(x_537);
x_545 = lean_ctor_get(x_540, 0);
lean_inc(x_545);
lean_dec(x_540);
lean_inc(x_533);
x_546 = l_Lean_isPrivateNameFromImportedModule(x_545, x_533);
lean_dec(x_545);
if (x_546 == 0)
{
lean_object* x_547; 
lean_dec(x_531);
lean_inc(x_3);
lean_inc(x_533);
x_547 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_533, x_3, x_4, x_5, x_6, x_7, x_8, x_541);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
lean_inc(x_548);
x_550 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_550, 0, x_548);
lean_closure_set(x_550, 1, x_536);
lean_closure_set(x_550, 2, x_543);
x_551 = lean_ctor_get(x_548, 0);
lean_inc(x_551);
lean_dec(x_548);
x_552 = lean_ctor_get(x_551, 2);
lean_inc(x_552);
lean_dec(x_551);
x_553 = lean_unbox(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_554 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_552, x_550, x_553, x_3, x_4, x_5, x_6, x_7, x_8, x_549);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = l_Lean_Syntax_TSepArray_getElems___redArg(x_544);
lean_dec(x_544);
x_558 = lean_array_get_size(x_557);
x_559 = lean_nat_dec_lt(x_558, x_555);
if (x_559 == 0)
{
uint8_t x_560; 
lean_free_object(x_66);
x_560 = lean_nat_dec_eq(x_558, x_555);
if (x_560 == 0)
{
uint8_t x_561; 
x_561 = lean_nat_dec_eq(x_555, x_543);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; size_t x_568; size_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_542);
lean_dec(x_535);
lean_free_object(x_59);
x_562 = lean_st_ref_get(x_8, x_556);
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_564 = x_562;
} else {
 lean_dec_ref(x_562);
 x_564 = lean_box(0);
}
x_565 = lean_nat_sub(x_555, x_536);
lean_dec(x_555);
lean_inc(x_565);
lean_inc(x_557);
x_566 = l_Array_toSubarray___redArg(x_557, x_565, x_558);
x_567 = l_Array_ofSubarray___redArg(x_566);
lean_dec(x_566);
x_568 = lean_array_size(x_567);
x_569 = lean_usize_of_nat(x_543);
x_570 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_568, x_569, x_567);
x_571 = l_Lean_mkAtom(x_538);
x_572 = lean_st_ref_get(x_8, x_563);
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_574 = x_572;
} else {
 lean_dec_ref(x_572);
 x_574 = lean_box(0);
}
x_575 = l_Lean_mkSepArray(x_570, x_571);
lean_dec(x_570);
x_576 = lean_ctor_get(x_7, 5);
lean_inc(x_576);
x_577 = lean_mk_string_unchecked("⟨", 3, 1);
x_578 = lean_mk_string_unchecked("null", 4, 4);
x_579 = l_Array_mkArray0(lean_box(0));
lean_inc(x_579);
x_580 = l_Array_append(lean_box(0), x_579, x_575);
lean_dec(x_575);
x_581 = lean_mk_string_unchecked("⟩", 3, 1);
x_582 = l_Lean_SourceInfo_fromRef(x_576, x_561);
lean_dec(x_576);
lean_inc(x_582);
if (lean_is_scalar(x_574)) {
 x_583 = lean_alloc_ctor(2, 2, 0);
} else {
 x_583 = x_574;
 lean_ctor_set_tag(x_583, 2);
}
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_577);
x_584 = l_Lean_Name_mkStr1(x_578);
lean_inc(x_584);
lean_inc(x_582);
x_585 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_584);
lean_ctor_set(x_585, 2, x_580);
lean_inc(x_582);
if (lean_is_scalar(x_564)) {
 x_586 = lean_alloc_ctor(2, 2, 0);
} else {
 x_586 = x_564;
 lean_ctor_set_tag(x_586, 2);
}
lean_ctor_set(x_586, 0, x_582);
lean_ctor_set(x_586, 1, x_581);
x_587 = l_Array_toSubarray___redArg(x_557, x_543, x_565);
lean_inc(x_582);
x_588 = l_Lean_Syntax_node3(x_582, x_14, x_583, x_585, x_586);
x_589 = l_Array_ofSubarray___redArg(x_587);
lean_dec(x_587);
x_590 = lean_array_push(x_589, x_588);
x_591 = lean_mk_string_unchecked("app", 3, 3);
x_592 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_591);
x_593 = l_Lean_mkCIdentFrom(x_1, x_533, x_15);
x_594 = l_Array_append(lean_box(0), x_579, x_590);
lean_dec(x_590);
lean_inc(x_582);
x_595 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_595, 0, x_582);
lean_ctor_set(x_595, 1, x_584);
lean_ctor_set(x_595, 2, x_594);
x_596 = l_Lean_Syntax_node2(x_582, x_592, x_593, x_595);
x_16 = x_596;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_573;
goto block_28;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_538);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_597 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_598 = l_Lean_stringToMessageData(x_597);
lean_dec(x_597);
x_599 = l_Lean_MessageData_ofName(x_533);
if (lean_is_scalar(x_542)) {
 x_600 = lean_alloc_ctor(7, 2, 0);
} else {
 x_600 = x_542;
 lean_ctor_set_tag(x_600, 7);
}
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_602 = l_Lean_stringToMessageData(x_601);
lean_dec(x_601);
if (lean_is_scalar(x_535)) {
 x_603 = lean_alloc_ctor(7, 2, 0);
} else {
 x_603 = x_535;
 lean_ctor_set_tag(x_603, 7);
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_602);
x_604 = l___private_Init_Data_Repr_0__Nat_reprFast(x_558);
x_605 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_605, 0, x_604);
x_606 = l_Lean_MessageData_ofFormat(x_605);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_606);
lean_ctor_set(x_59, 0, x_603);
x_607 = lean_mk_string_unchecked(" provided", 9, 9);
x_608 = l_Lean_stringToMessageData(x_607);
lean_dec(x_607);
x_609 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_609, 0, x_59);
lean_ctor_set(x_609, 1, x_608);
x_610 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_609, x_3, x_4, x_5, x_6, x_7, x_8, x_556);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_613 = x_610;
} else {
 lean_dec_ref(x_610);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_612);
return x_614;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_542);
lean_dec(x_538);
lean_dec(x_535);
lean_free_object(x_59);
lean_dec(x_14);
x_615 = lean_st_ref_get(x_8, x_556);
x_616 = lean_ctor_get(x_615, 1);
lean_inc(x_616);
lean_dec(x_615);
x_617 = lean_ctor_get(x_7, 5);
lean_inc(x_617);
x_618 = lean_unbox(x_64);
x_619 = l_Lean_SourceInfo_fromRef(x_617, x_618);
lean_dec(x_617);
x_620 = lean_mk_string_unchecked("app", 3, 3);
x_621 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_620);
x_622 = l_Lean_mkCIdentFrom(x_1, x_533, x_15);
x_623 = lean_mk_string_unchecked("null", 4, 4);
x_624 = l_Lean_Name_mkStr1(x_623);
x_625 = l_Array_mkArray0(lean_box(0));
x_626 = l_Array_append(lean_box(0), x_625, x_557);
lean_dec(x_557);
lean_inc(x_619);
x_627 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_627, 0, x_619);
lean_ctor_set(x_627, 1, x_624);
lean_ctor_set(x_627, 2, x_626);
x_628 = l_Lean_Syntax_node2(x_619, x_621, x_622, x_627);
x_16 = x_628;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_616;
goto block_28;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_557);
lean_dec(x_538);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_629 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_630 = l_Lean_stringToMessageData(x_629);
lean_dec(x_629);
x_631 = l_Lean_MessageData_ofName(x_533);
if (lean_is_scalar(x_542)) {
 x_632 = lean_alloc_ctor(7, 2, 0);
} else {
 x_632 = x_542;
 lean_ctor_set_tag(x_632, 7);
}
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
x_633 = lean_mk_string_unchecked("' has #", 7, 7);
x_634 = l_Lean_stringToMessageData(x_633);
lean_dec(x_633);
if (lean_is_scalar(x_535)) {
 x_635 = lean_alloc_ctor(7, 2, 0);
} else {
 x_635 = x_535;
 lean_ctor_set_tag(x_635, 7);
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_634);
x_636 = l___private_Init_Data_Repr_0__Nat_reprFast(x_555);
x_637 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_637, 0, x_636);
x_638 = l_Lean_MessageData_ofFormat(x_637);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_638);
lean_ctor_set(x_59, 0, x_635);
x_639 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_640 = l_Lean_stringToMessageData(x_639);
lean_dec(x_639);
x_641 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_641, 0, x_59);
lean_ctor_set(x_641, 1, x_640);
x_642 = l___private_Init_Data_Repr_0__Nat_reprFast(x_558);
lean_ctor_set_tag(x_66, 3);
lean_ctor_set(x_66, 0, x_642);
x_643 = l_Lean_MessageData_ofFormat(x_66);
x_644 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_644, 0, x_641);
lean_ctor_set(x_644, 1, x_643);
x_645 = lean_mk_string_unchecked(" provided", 9, 9);
x_646 = l_Lean_stringToMessageData(x_645);
lean_dec(x_645);
x_647 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_647, x_3, x_4, x_5, x_6, x_7, x_8, x_556);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_651 = x_648;
} else {
 lean_dec_ref(x_648);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_538);
lean_dec(x_535);
lean_dec(x_533);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_653 = lean_ctor_get(x_554, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_554, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_655 = x_554;
} else {
 lean_dec_ref(x_554);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_538);
lean_dec(x_535);
lean_dec(x_533);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
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
x_657 = lean_ctor_get(x_547, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_547, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_659 = x_547;
} else {
 lean_dec_ref(x_547);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_544);
lean_dec(x_538);
lean_dec(x_533);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_661 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_662 = l_Lean_stringToMessageData(x_661);
lean_dec(x_661);
x_663 = lean_ctor_get(x_531, 0);
lean_inc(x_663);
lean_dec(x_531);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
lean_dec(x_663);
x_665 = l_Lean_MessageData_ofName(x_664);
if (lean_is_scalar(x_542)) {
 x_666 = lean_alloc_ctor(7, 2, 0);
} else {
 x_666 = x_542;
 lean_ctor_set_tag(x_666, 7);
}
lean_ctor_set(x_666, 0, x_662);
lean_ctor_set(x_666, 1, x_665);
x_667 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_668 = l_Lean_stringToMessageData(x_667);
lean_dec(x_667);
if (lean_is_scalar(x_535)) {
 x_669 = lean_alloc_ctor(7, 2, 0);
} else {
 x_669 = x_535;
 lean_ctor_set_tag(x_669, 7);
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_668);
x_670 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_669, x_3, x_4, x_5, x_6, x_7, x_8, x_541);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_673 = x_670;
} else {
 lean_dec_ref(x_670);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
else
{
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_534);
lean_dec(x_533);
lean_dec(x_531);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
}
}
}
else
{
lean_object* x_675; lean_object* x_676; 
lean_free_object(x_66);
lean_dec(x_70);
lean_free_object(x_59);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_675 = lean_box(0);
x_676 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_675, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_676;
}
}
else
{
lean_object* x_677; 
x_677 = lean_ctor_get(x_66, 0);
lean_inc(x_677);
lean_dec(x_66);
if (lean_obj_tag(x_677) == 5)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 x_679 = x_677;
} else {
 lean_dec_ref(x_677);
 x_679 = lean_box(0);
}
x_680 = lean_ctor_get(x_678, 4);
lean_inc(x_680);
if (lean_obj_tag(x_680) == 0)
{
lean_dec(x_679);
lean_dec(x_678);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
x_684 = lean_unsigned_to_nat(1u);
x_685 = l_Lean_Syntax_getArg(x_1, x_684);
x_686 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
lean_dec(x_40);
lean_dec(x_38);
x_687 = lean_st_ref_get(x_8, x_62);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_690 = x_687;
} else {
 lean_dec_ref(x_687);
 x_690 = lean_box(0);
}
x_691 = lean_unsigned_to_nat(0u);
x_692 = l_Lean_Syntax_getArgs(x_685);
lean_dec(x_685);
x_693 = lean_ctor_get(x_688, 0);
lean_inc(x_693);
lean_dec(x_688);
lean_inc(x_681);
x_694 = l_Lean_isPrivateNameFromImportedModule(x_693, x_681);
lean_dec(x_693);
if (x_694 == 0)
{
lean_object* x_695; 
lean_dec(x_678);
lean_inc(x_3);
lean_inc(x_681);
x_695 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_681, x_3, x_4, x_5, x_6, x_7, x_8, x_689);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; lean_object* x_702; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
lean_inc(x_696);
x_698 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_698, 0, x_696);
lean_closure_set(x_698, 1, x_684);
lean_closure_set(x_698, 2, x_691);
x_699 = lean_ctor_get(x_696, 0);
lean_inc(x_699);
lean_dec(x_696);
x_700 = lean_ctor_get(x_699, 2);
lean_inc(x_700);
lean_dec(x_699);
x_701 = lean_unbox(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_702 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_700, x_698, x_701, x_3, x_4, x_5, x_6, x_7, x_8, x_697);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_705 = l_Lean_Syntax_TSepArray_getElems___redArg(x_692);
lean_dec(x_692);
x_706 = lean_array_get_size(x_705);
x_707 = lean_nat_dec_lt(x_706, x_703);
if (x_707 == 0)
{
uint8_t x_708; 
x_708 = lean_nat_dec_eq(x_706, x_703);
if (x_708 == 0)
{
uint8_t x_709; 
x_709 = lean_nat_dec_eq(x_703, x_691);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; size_t x_716; size_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_690);
lean_dec(x_683);
lean_dec(x_679);
lean_free_object(x_59);
x_710 = lean_st_ref_get(x_8, x_704);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_712 = x_710;
} else {
 lean_dec_ref(x_710);
 x_712 = lean_box(0);
}
x_713 = lean_nat_sub(x_703, x_684);
lean_dec(x_703);
lean_inc(x_713);
lean_inc(x_705);
x_714 = l_Array_toSubarray___redArg(x_705, x_713, x_706);
x_715 = l_Array_ofSubarray___redArg(x_714);
lean_dec(x_714);
x_716 = lean_array_size(x_715);
x_717 = lean_usize_of_nat(x_691);
x_718 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_716, x_717, x_715);
x_719 = l_Lean_mkAtom(x_686);
x_720 = lean_st_ref_get(x_8, x_711);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
x_723 = l_Lean_mkSepArray(x_718, x_719);
lean_dec(x_718);
x_724 = lean_ctor_get(x_7, 5);
lean_inc(x_724);
x_725 = lean_mk_string_unchecked("⟨", 3, 1);
x_726 = lean_mk_string_unchecked("null", 4, 4);
x_727 = l_Array_mkArray0(lean_box(0));
lean_inc(x_727);
x_728 = l_Array_append(lean_box(0), x_727, x_723);
lean_dec(x_723);
x_729 = lean_mk_string_unchecked("⟩", 3, 1);
x_730 = l_Lean_SourceInfo_fromRef(x_724, x_709);
lean_dec(x_724);
lean_inc(x_730);
if (lean_is_scalar(x_722)) {
 x_731 = lean_alloc_ctor(2, 2, 0);
} else {
 x_731 = x_722;
 lean_ctor_set_tag(x_731, 2);
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_725);
x_732 = l_Lean_Name_mkStr1(x_726);
lean_inc(x_732);
lean_inc(x_730);
x_733 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_733, 0, x_730);
lean_ctor_set(x_733, 1, x_732);
lean_ctor_set(x_733, 2, x_728);
lean_inc(x_730);
if (lean_is_scalar(x_712)) {
 x_734 = lean_alloc_ctor(2, 2, 0);
} else {
 x_734 = x_712;
 lean_ctor_set_tag(x_734, 2);
}
lean_ctor_set(x_734, 0, x_730);
lean_ctor_set(x_734, 1, x_729);
x_735 = l_Array_toSubarray___redArg(x_705, x_691, x_713);
lean_inc(x_730);
x_736 = l_Lean_Syntax_node3(x_730, x_14, x_731, x_733, x_734);
x_737 = l_Array_ofSubarray___redArg(x_735);
lean_dec(x_735);
x_738 = lean_array_push(x_737, x_736);
x_739 = lean_mk_string_unchecked("app", 3, 3);
x_740 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_739);
x_741 = l_Lean_mkCIdentFrom(x_1, x_681, x_15);
x_742 = l_Array_append(lean_box(0), x_727, x_738);
lean_dec(x_738);
lean_inc(x_730);
x_743 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_743, 0, x_730);
lean_ctor_set(x_743, 1, x_732);
lean_ctor_set(x_743, 2, x_742);
x_744 = l_Lean_Syntax_node2(x_730, x_740, x_741, x_743);
x_16 = x_744;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_721;
goto block_28;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_705);
lean_dec(x_703);
lean_dec(x_686);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_745 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_746 = l_Lean_stringToMessageData(x_745);
lean_dec(x_745);
x_747 = l_Lean_MessageData_ofName(x_681);
if (lean_is_scalar(x_690)) {
 x_748 = lean_alloc_ctor(7, 2, 0);
} else {
 x_748 = x_690;
 lean_ctor_set_tag(x_748, 7);
}
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
x_749 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_750 = l_Lean_stringToMessageData(x_749);
lean_dec(x_749);
if (lean_is_scalar(x_683)) {
 x_751 = lean_alloc_ctor(7, 2, 0);
} else {
 x_751 = x_683;
 lean_ctor_set_tag(x_751, 7);
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_750);
x_752 = l___private_Init_Data_Repr_0__Nat_reprFast(x_706);
if (lean_is_scalar(x_679)) {
 x_753 = lean_alloc_ctor(3, 1, 0);
} else {
 x_753 = x_679;
 lean_ctor_set_tag(x_753, 3);
}
lean_ctor_set(x_753, 0, x_752);
x_754 = l_Lean_MessageData_ofFormat(x_753);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_754);
lean_ctor_set(x_59, 0, x_751);
x_755 = lean_mk_string_unchecked(" provided", 9, 9);
x_756 = l_Lean_stringToMessageData(x_755);
lean_dec(x_755);
x_757 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_757, 0, x_59);
lean_ctor_set(x_757, 1, x_756);
x_758 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_757, x_3, x_4, x_5, x_6, x_7, x_8, x_704);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_761 = x_758;
} else {
 lean_dec_ref(x_758);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_706);
lean_dec(x_703);
lean_dec(x_690);
lean_dec(x_686);
lean_dec(x_683);
lean_dec(x_679);
lean_free_object(x_59);
lean_dec(x_14);
x_763 = lean_st_ref_get(x_8, x_704);
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
lean_dec(x_763);
x_765 = lean_ctor_get(x_7, 5);
lean_inc(x_765);
x_766 = lean_unbox(x_64);
x_767 = l_Lean_SourceInfo_fromRef(x_765, x_766);
lean_dec(x_765);
x_768 = lean_mk_string_unchecked("app", 3, 3);
x_769 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_768);
x_770 = l_Lean_mkCIdentFrom(x_1, x_681, x_15);
x_771 = lean_mk_string_unchecked("null", 4, 4);
x_772 = l_Lean_Name_mkStr1(x_771);
x_773 = l_Array_mkArray0(lean_box(0));
x_774 = l_Array_append(lean_box(0), x_773, x_705);
lean_dec(x_705);
lean_inc(x_767);
x_775 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_775, 0, x_767);
lean_ctor_set(x_775, 1, x_772);
lean_ctor_set(x_775, 2, x_774);
x_776 = l_Lean_Syntax_node2(x_767, x_769, x_770, x_775);
x_16 = x_776;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_764;
goto block_28;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_705);
lean_dec(x_686);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_777 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_778 = l_Lean_stringToMessageData(x_777);
lean_dec(x_777);
x_779 = l_Lean_MessageData_ofName(x_681);
if (lean_is_scalar(x_690)) {
 x_780 = lean_alloc_ctor(7, 2, 0);
} else {
 x_780 = x_690;
 lean_ctor_set_tag(x_780, 7);
}
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
x_781 = lean_mk_string_unchecked("' has #", 7, 7);
x_782 = l_Lean_stringToMessageData(x_781);
lean_dec(x_781);
if (lean_is_scalar(x_683)) {
 x_783 = lean_alloc_ctor(7, 2, 0);
} else {
 x_783 = x_683;
 lean_ctor_set_tag(x_783, 7);
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_782);
x_784 = l___private_Init_Data_Repr_0__Nat_reprFast(x_703);
if (lean_is_scalar(x_679)) {
 x_785 = lean_alloc_ctor(3, 1, 0);
} else {
 x_785 = x_679;
 lean_ctor_set_tag(x_785, 3);
}
lean_ctor_set(x_785, 0, x_784);
x_786 = l_Lean_MessageData_ofFormat(x_785);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_786);
lean_ctor_set(x_59, 0, x_783);
x_787 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_788 = l_Lean_stringToMessageData(x_787);
lean_dec(x_787);
x_789 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_789, 0, x_59);
lean_ctor_set(x_789, 1, x_788);
x_790 = l___private_Init_Data_Repr_0__Nat_reprFast(x_706);
x_791 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_791, 0, x_790);
x_792 = l_Lean_MessageData_ofFormat(x_791);
x_793 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_793, 0, x_789);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_mk_string_unchecked(" provided", 9, 9);
x_795 = l_Lean_stringToMessageData(x_794);
lean_dec(x_794);
x_796 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_795);
x_797 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_796, x_3, x_4, x_5, x_6, x_7, x_8, x_704);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_800 = x_797;
} else {
 lean_dec_ref(x_797);
 x_800 = lean_box(0);
}
if (lean_is_scalar(x_800)) {
 x_801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_801 = x_800;
}
lean_ctor_set(x_801, 0, x_798);
lean_ctor_set(x_801, 1, x_799);
return x_801;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_686);
lean_dec(x_683);
lean_dec(x_681);
lean_dec(x_679);
lean_free_object(x_59);
lean_dec(x_14);
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
x_802 = lean_ctor_get(x_702, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_702, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_804 = x_702;
} else {
 lean_dec_ref(x_702);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_686);
lean_dec(x_683);
lean_dec(x_681);
lean_dec(x_679);
lean_free_object(x_59);
lean_dec(x_14);
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
x_806 = lean_ctor_get(x_695, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_695, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_808 = x_695;
} else {
 lean_dec_ref(x_695);
 x_808 = lean_box(0);
}
if (lean_is_scalar(x_808)) {
 x_809 = lean_alloc_ctor(1, 2, 0);
} else {
 x_809 = x_808;
}
lean_ctor_set(x_809, 0, x_806);
lean_ctor_set(x_809, 1, x_807);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_692);
lean_dec(x_686);
lean_dec(x_681);
lean_dec(x_679);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_810 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_811 = l_Lean_stringToMessageData(x_810);
lean_dec(x_810);
x_812 = lean_ctor_get(x_678, 0);
lean_inc(x_812);
lean_dec(x_678);
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
lean_dec(x_812);
x_814 = l_Lean_MessageData_ofName(x_813);
if (lean_is_scalar(x_690)) {
 x_815 = lean_alloc_ctor(7, 2, 0);
} else {
 x_815 = x_690;
 lean_ctor_set_tag(x_815, 7);
}
lean_ctor_set(x_815, 0, x_811);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_817 = l_Lean_stringToMessageData(x_816);
lean_dec(x_816);
if (lean_is_scalar(x_683)) {
 x_818 = lean_alloc_ctor(7, 2, 0);
} else {
 x_818 = x_683;
 lean_ctor_set_tag(x_818, 7);
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_817);
x_819 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_818, x_3, x_4, x_5, x_6, x_7, x_8, x_689);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_820);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
else
{
lean_dec(x_686);
lean_dec(x_685);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_679);
lean_dec(x_678);
lean_free_object(x_59);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_62;
goto block_56;
}
}
}
else
{
lean_object* x_824; lean_object* x_825; 
lean_dec(x_677);
lean_free_object(x_59);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_824 = lean_box(0);
x_825 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_824, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_825;
}
}
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; lean_object* x_831; 
x_826 = lean_ctor_get(x_59, 0);
x_827 = lean_ctor_get(x_59, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_59);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_box(0);
x_830 = lean_unbox(x_829);
x_831 = l_Lean_Environment_find_x3f(x_828, x_58, x_830);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; 
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_832 = lean_box(0);
x_833 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_832, x_3, x_4, x_5, x_6, x_7, x_8, x_827);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; 
x_834 = lean_ctor_get(x_831, 0);
lean_inc(x_834);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 x_835 = x_831;
} else {
 lean_dec_ref(x_831);
 x_835 = lean_box(0);
}
if (lean_obj_tag(x_834) == 5)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_834, 0);
lean_inc(x_836);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 x_837 = x_834;
} else {
 lean_dec_ref(x_834);
 x_837 = lean_box(0);
}
x_838 = lean_ctor_get(x_836, 4);
lean_inc(x_838);
if (lean_obj_tag(x_838) == 0)
{
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_827;
goto block_56;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_841 = x_838;
} else {
 lean_dec_ref(x_838);
 x_841 = lean_box(0);
}
x_842 = lean_unsigned_to_nat(1u);
x_843 = l_Lean_Syntax_getArg(x_1, x_842);
x_844 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; 
lean_dec(x_40);
lean_dec(x_38);
x_845 = lean_st_ref_get(x_8, x_827);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_848 = x_845;
} else {
 lean_dec_ref(x_845);
 x_848 = lean_box(0);
}
x_849 = lean_unsigned_to_nat(0u);
x_850 = l_Lean_Syntax_getArgs(x_843);
lean_dec(x_843);
x_851 = lean_ctor_get(x_846, 0);
lean_inc(x_851);
lean_dec(x_846);
lean_inc(x_839);
x_852 = l_Lean_isPrivateNameFromImportedModule(x_851, x_839);
lean_dec(x_851);
if (x_852 == 0)
{
lean_object* x_853; 
lean_dec(x_836);
lean_inc(x_3);
lean_inc(x_839);
x_853 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_839, x_3, x_4, x_5, x_6, x_7, x_8, x_847);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; lean_object* x_860; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
lean_inc(x_854);
x_856 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed), 12, 3);
lean_closure_set(x_856, 0, x_854);
lean_closure_set(x_856, 1, x_842);
lean_closure_set(x_856, 2, x_849);
x_857 = lean_ctor_get(x_854, 0);
lean_inc(x_857);
lean_dec(x_854);
x_858 = lean_ctor_get(x_857, 2);
lean_inc(x_858);
lean_dec(x_857);
x_859 = lean_unbox(x_829);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_860 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_858, x_856, x_859, x_3, x_4, x_5, x_6, x_7, x_8, x_855);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; uint8_t x_865; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = l_Lean_Syntax_TSepArray_getElems___redArg(x_850);
lean_dec(x_850);
x_864 = lean_array_get_size(x_863);
x_865 = lean_nat_dec_lt(x_864, x_861);
if (x_865 == 0)
{
uint8_t x_866; 
lean_dec(x_835);
x_866 = lean_nat_dec_eq(x_864, x_861);
if (x_866 == 0)
{
uint8_t x_867; 
x_867 = lean_nat_dec_eq(x_861, x_849);
if (x_867 == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; size_t x_874; size_t x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_848);
lean_dec(x_841);
lean_dec(x_837);
x_868 = lean_st_ref_get(x_8, x_862);
x_869 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_870 = x_868;
} else {
 lean_dec_ref(x_868);
 x_870 = lean_box(0);
}
x_871 = lean_nat_sub(x_861, x_842);
lean_dec(x_861);
lean_inc(x_871);
lean_inc(x_863);
x_872 = l_Array_toSubarray___redArg(x_863, x_871, x_864);
x_873 = l_Array_ofSubarray___redArg(x_872);
lean_dec(x_872);
x_874 = lean_array_size(x_873);
x_875 = lean_usize_of_nat(x_849);
x_876 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_874, x_875, x_873);
x_877 = l_Lean_mkAtom(x_844);
x_878 = lean_st_ref_get(x_8, x_869);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_880 = x_878;
} else {
 lean_dec_ref(x_878);
 x_880 = lean_box(0);
}
x_881 = l_Lean_mkSepArray(x_876, x_877);
lean_dec(x_876);
x_882 = lean_ctor_get(x_7, 5);
lean_inc(x_882);
x_883 = lean_mk_string_unchecked("⟨", 3, 1);
x_884 = lean_mk_string_unchecked("null", 4, 4);
x_885 = l_Array_mkArray0(lean_box(0));
lean_inc(x_885);
x_886 = l_Array_append(lean_box(0), x_885, x_881);
lean_dec(x_881);
x_887 = lean_mk_string_unchecked("⟩", 3, 1);
x_888 = l_Lean_SourceInfo_fromRef(x_882, x_867);
lean_dec(x_882);
lean_inc(x_888);
if (lean_is_scalar(x_880)) {
 x_889 = lean_alloc_ctor(2, 2, 0);
} else {
 x_889 = x_880;
 lean_ctor_set_tag(x_889, 2);
}
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_883);
x_890 = l_Lean_Name_mkStr1(x_884);
lean_inc(x_890);
lean_inc(x_888);
x_891 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_891, 0, x_888);
lean_ctor_set(x_891, 1, x_890);
lean_ctor_set(x_891, 2, x_886);
lean_inc(x_888);
if (lean_is_scalar(x_870)) {
 x_892 = lean_alloc_ctor(2, 2, 0);
} else {
 x_892 = x_870;
 lean_ctor_set_tag(x_892, 2);
}
lean_ctor_set(x_892, 0, x_888);
lean_ctor_set(x_892, 1, x_887);
x_893 = l_Array_toSubarray___redArg(x_863, x_849, x_871);
lean_inc(x_888);
x_894 = l_Lean_Syntax_node3(x_888, x_14, x_889, x_891, x_892);
x_895 = l_Array_ofSubarray___redArg(x_893);
lean_dec(x_893);
x_896 = lean_array_push(x_895, x_894);
x_897 = lean_mk_string_unchecked("app", 3, 3);
x_898 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_897);
x_899 = l_Lean_mkCIdentFrom(x_1, x_839, x_15);
x_900 = l_Array_append(lean_box(0), x_885, x_896);
lean_dec(x_896);
lean_inc(x_888);
x_901 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_901, 0, x_888);
lean_ctor_set(x_901, 1, x_890);
lean_ctor_set(x_901, 2, x_900);
x_902 = l_Lean_Syntax_node2(x_888, x_898, x_899, x_901);
x_16 = x_902;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_879;
goto block_28;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_844);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_903 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_904 = l_Lean_stringToMessageData(x_903);
lean_dec(x_903);
x_905 = l_Lean_MessageData_ofName(x_839);
if (lean_is_scalar(x_848)) {
 x_906 = lean_alloc_ctor(7, 2, 0);
} else {
 x_906 = x_848;
 lean_ctor_set_tag(x_906, 7);
}
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
x_907 = lean_mk_string_unchecked("' does not have explicit fields, but #", 38, 38);
x_908 = l_Lean_stringToMessageData(x_907);
lean_dec(x_907);
if (lean_is_scalar(x_841)) {
 x_909 = lean_alloc_ctor(7, 2, 0);
} else {
 x_909 = x_841;
 lean_ctor_set_tag(x_909, 7);
}
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_908);
x_910 = l___private_Init_Data_Repr_0__Nat_reprFast(x_864);
if (lean_is_scalar(x_837)) {
 x_911 = lean_alloc_ctor(3, 1, 0);
} else {
 x_911 = x_837;
 lean_ctor_set_tag(x_911, 3);
}
lean_ctor_set(x_911, 0, x_910);
x_912 = l_Lean_MessageData_ofFormat(x_911);
x_913 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_913, 0, x_909);
lean_ctor_set(x_913, 1, x_912);
x_914 = lean_mk_string_unchecked(" provided", 9, 9);
x_915 = l_Lean_stringToMessageData(x_914);
lean_dec(x_914);
x_916 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_916, 0, x_913);
lean_ctor_set(x_916, 1, x_915);
x_917 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_916, x_3, x_4, x_5, x_6, x_7, x_8, x_862);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_920 = x_917;
} else {
 lean_dec_ref(x_917);
 x_920 = lean_box(0);
}
if (lean_is_scalar(x_920)) {
 x_921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_921 = x_920;
}
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_919);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_864);
lean_dec(x_861);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_841);
lean_dec(x_837);
lean_dec(x_14);
x_922 = lean_st_ref_get(x_8, x_862);
x_923 = lean_ctor_get(x_922, 1);
lean_inc(x_923);
lean_dec(x_922);
x_924 = lean_ctor_get(x_7, 5);
lean_inc(x_924);
x_925 = lean_unbox(x_829);
x_926 = l_Lean_SourceInfo_fromRef(x_924, x_925);
lean_dec(x_924);
x_927 = lean_mk_string_unchecked("app", 3, 3);
x_928 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_927);
x_929 = l_Lean_mkCIdentFrom(x_1, x_839, x_15);
x_930 = lean_mk_string_unchecked("null", 4, 4);
x_931 = l_Lean_Name_mkStr1(x_930);
x_932 = l_Array_mkArray0(lean_box(0));
x_933 = l_Array_append(lean_box(0), x_932, x_863);
lean_dec(x_863);
lean_inc(x_926);
x_934 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_934, 0, x_926);
lean_ctor_set(x_934, 1, x_931);
lean_ctor_set(x_934, 2, x_933);
x_935 = l_Lean_Syntax_node2(x_926, x_928, x_929, x_934);
x_16 = x_935;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_923;
goto block_28;
}
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
lean_dec(x_863);
lean_dec(x_844);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_936 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '", 77, 73);
x_937 = l_Lean_stringToMessageData(x_936);
lean_dec(x_936);
x_938 = l_Lean_MessageData_ofName(x_839);
if (lean_is_scalar(x_848)) {
 x_939 = lean_alloc_ctor(7, 2, 0);
} else {
 x_939 = x_848;
 lean_ctor_set_tag(x_939, 7);
}
lean_ctor_set(x_939, 0, x_937);
lean_ctor_set(x_939, 1, x_938);
x_940 = lean_mk_string_unchecked("' has #", 7, 7);
x_941 = l_Lean_stringToMessageData(x_940);
lean_dec(x_940);
if (lean_is_scalar(x_841)) {
 x_942 = lean_alloc_ctor(7, 2, 0);
} else {
 x_942 = x_841;
 lean_ctor_set_tag(x_942, 7);
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_941);
x_943 = l___private_Init_Data_Repr_0__Nat_reprFast(x_861);
if (lean_is_scalar(x_837)) {
 x_944 = lean_alloc_ctor(3, 1, 0);
} else {
 x_944 = x_837;
 lean_ctor_set_tag(x_944, 3);
}
lean_ctor_set(x_944, 0, x_943);
x_945 = l_Lean_MessageData_ofFormat(x_944);
x_946 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_946, 0, x_942);
lean_ctor_set(x_946, 1, x_945);
x_947 = lean_mk_string_unchecked(" explicit fields, but only #", 28, 28);
x_948 = l_Lean_stringToMessageData(x_947);
lean_dec(x_947);
x_949 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_949, 0, x_946);
lean_ctor_set(x_949, 1, x_948);
x_950 = l___private_Init_Data_Repr_0__Nat_reprFast(x_864);
if (lean_is_scalar(x_835)) {
 x_951 = lean_alloc_ctor(3, 1, 0);
} else {
 x_951 = x_835;
 lean_ctor_set_tag(x_951, 3);
}
lean_ctor_set(x_951, 0, x_950);
x_952 = l_Lean_MessageData_ofFormat(x_951);
x_953 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_953, 0, x_949);
lean_ctor_set(x_953, 1, x_952);
x_954 = lean_mk_string_unchecked(" provided", 9, 9);
x_955 = l_Lean_stringToMessageData(x_954);
lean_dec(x_954);
x_956 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_956, 0, x_953);
lean_ctor_set(x_956, 1, x_955);
x_957 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_956, x_3, x_4, x_5, x_6, x_7, x_8, x_862);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_960)) {
 x_961 = lean_alloc_ctor(1, 2, 0);
} else {
 x_961 = x_960;
}
lean_ctor_set(x_961, 0, x_958);
lean_ctor_set(x_961, 1, x_959);
return x_961;
}
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_14);
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
x_962 = lean_ctor_get(x_860, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_860, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_964 = x_860;
} else {
 lean_dec_ref(x_860);
 x_964 = lean_box(0);
}
if (lean_is_scalar(x_964)) {
 x_965 = lean_alloc_ctor(1, 2, 0);
} else {
 x_965 = x_964;
}
lean_ctor_set(x_965, 0, x_962);
lean_ctor_set(x_965, 1, x_963);
return x_965;
}
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_14);
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
x_966 = lean_ctor_get(x_853, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_853, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_968 = x_853;
} else {
 lean_dec_ref(x_853);
 x_968 = lean_box(0);
}
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(1, 2, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_966);
lean_ctor_set(x_969, 1, x_967);
return x_969;
}
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_850);
lean_dec(x_844);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_970 = lean_mk_string_unchecked("invalid ⟨...⟩ notation, constructor for `", 45, 41);
x_971 = l_Lean_stringToMessageData(x_970);
lean_dec(x_970);
x_972 = lean_ctor_get(x_836, 0);
lean_inc(x_972);
lean_dec(x_836);
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
lean_dec(x_972);
x_974 = l_Lean_MessageData_ofName(x_973);
if (lean_is_scalar(x_848)) {
 x_975 = lean_alloc_ctor(7, 2, 0);
} else {
 x_975 = x_848;
 lean_ctor_set_tag(x_975, 7);
}
lean_ctor_set(x_975, 0, x_971);
lean_ctor_set(x_975, 1, x_974);
x_976 = lean_mk_string_unchecked("` is marked as private", 22, 22);
x_977 = l_Lean_stringToMessageData(x_976);
lean_dec(x_976);
if (lean_is_scalar(x_841)) {
 x_978 = lean_alloc_ctor(7, 2, 0);
} else {
 x_978 = x_841;
 lean_ctor_set_tag(x_978, 7);
}
lean_ctor_set(x_978, 0, x_975);
lean_ctor_set(x_978, 1, x_977);
x_979 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_978, x_3, x_4, x_5, x_6, x_7, x_8, x_847);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_982 = x_979;
} else {
 lean_dec_ref(x_979);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
}
else
{
lean_dec(x_844);
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_827;
goto block_56;
}
}
}
else
{
lean_object* x_984; lean_object* x_985; 
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_984 = lean_box(0);
x_985 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_984, x_3, x_4, x_5, x_6, x_7, x_8, x_827);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_985;
}
}
}
}
else
{
lean_object* x_986; lean_object* x_987; 
lean_dec(x_57);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_986 = lean_box(0);
x_987 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_38, x_986, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_987;
}
block_56:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_mk_string_unchecked("invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor ", 97, 93);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = l_Lean_indentExpr(x_38);
if (lean_is_scalar(x_40)) {
 x_51 = lean_alloc_ctor(7, 2, 0);
} else {
 x_51 = x_40;
 lean_ctor_set_tag(x_51, 7);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("", 0, 0);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_54, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
return x_55;
}
}
else
{
lean_dec(x_14);
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
return x_37;
}
}
}
else
{
uint8_t x_988; 
lean_dec(x_14);
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
x_988 = !lean_is_exclusive(x_30);
if (x_988 == 0)
{
return x_30;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_30, 0);
x_990 = lean_ctor_get(x_30, 1);
lean_inc(x_990);
lean_inc(x_989);
lean_dec(x_30);
x_991 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_991, 0, x_989);
lean_ctor_set(x_991, 1, x_990);
return x_991;
}
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(x_15);
x_25 = lean_box(x_15);
lean_inc(x_16);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_25);
x_27 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_16, x_26, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Term_elabAnonymousCtor_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Elab_Term_elabAnonymousCtor_spec__3(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabAnonymousCtor___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_elabAnonymousCtor___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("anonymousCtor", 13, 13);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabAnonymousCtor", 17, 17);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabAnonymousCtor", 17, 17);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(41u);
x_8 = lean_unsigned_to_nat(35u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(77u);
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
x_16 = lean_unsigned_to_nat(56u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("borrowed", 8, 8);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_elabTerm(x_18, x_2, x_15, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_markBorrowed(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = l_Lean_markBorrowed(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBorrowed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabBorrowed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("borrowed", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabBorrowed", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBorrowed___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabBorrowed", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(79u);
x_8 = lean_unsigned_to_nat(30u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(82u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandShow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("show", 4, 4);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_mk_string_unchecked("byTactic'", 9, 9);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Syntax_getArg(x_12, x_18);
x_21 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_SourceInfo_fromRef(x_22, x_24);
lean_inc(x_25);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_mk_string_unchecked("fromTerm", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("from", 4, 4);
lean_inc(x_25);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("byTactic", 8, 8);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_21, x_15);
lean_dec(x_21);
x_34 = lean_mk_string_unchecked("by", 2, 2);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_25);
x_36 = l_Lean_Syntax_node2(x_25, x_32, x_35, x_20);
lean_inc(x_25);
x_37 = l_Lean_Syntax_node2(x_25, x_28, x_30, x_36);
x_38 = l_Lean_Syntax_node3(x_25, x_8, x_26, x_19, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandShow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandShow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("show", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandShow", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandShow___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandShow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandShow", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(84u);
x_8 = lean_unsigned_to_nat(39u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(87u);
x_11 = lean_unsigned_to_nat(54u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(53u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabShow___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_11);
x_14 = l_Lean_Meta_isExprDefEq(x_13, x_11, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabShow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("show", 4, 4);
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
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_mk_string_unchecked("fromTerm", 8, 8);
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
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabShow___lam__0), 9, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_2);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_25, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Elab_Term_exprToSyntax(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_8, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_mk_string_unchecked("this", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = lean_box(0);
x_42 = lean_ctor_get(x_7, 5);
lean_inc(x_42);
x_43 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_44 = lean_unbox(x_41);
x_45 = l_Lean_SourceInfo_fromRef(x_42, x_44);
lean_dec(x_42);
x_46 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_47 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_46);
lean_inc(x_45);
lean_ctor_set_tag(x_35, 2);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_45);
x_48 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_49 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_48);
x_50 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_51 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_50);
x_52 = lean_unbox(x_41);
x_53 = l_Lean_mkIdentFrom(x_1, x_40, x_52);
lean_dec(x_1);
x_54 = lean_mk_string_unchecked("null", 4, 4);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Array_mkArray0(lean_box(0));
lean_inc(x_55);
lean_inc(x_45);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_59 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_58);
x_60 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_45);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_60);
lean_ctor_set(x_28, 0, x_45);
lean_inc(x_45);
x_61 = l_Lean_Syntax_node2(x_45, x_59, x_28, x_33);
lean_inc(x_45);
x_62 = l_Lean_Syntax_node1(x_45, x_55, x_61);
x_63 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_45);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_53);
lean_inc(x_45);
x_65 = l_Lean_Syntax_node5(x_45, x_51, x_53, x_57, x_62, x_64, x_43);
lean_inc(x_45);
x_66 = l_Lean_Syntax_node1(x_45, x_49, x_65);
x_67 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_45);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Syntax_node4(x_45, x_47, x_35, x_66, x_68, x_53);
x_70 = l_Lean_Elab_Term_elabTerm(x_69, x_2, x_21, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_7);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_dec(x_35);
x_72 = lean_mk_string_unchecked("this", 4, 4);
x_73 = l_Lean_Name_mkStr1(x_72);
x_74 = lean_box(0);
x_75 = lean_ctor_get(x_7, 5);
lean_inc(x_75);
x_76 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_77 = lean_unbox(x_74);
x_78 = l_Lean_SourceInfo_fromRef(x_75, x_77);
lean_dec(x_75);
x_79 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_79);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_80 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_79);
lean_inc(x_78);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_83 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_82);
x_84 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_85 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_84);
x_86 = lean_unbox(x_74);
x_87 = l_Lean_mkIdentFrom(x_1, x_73, x_86);
lean_dec(x_1);
x_88 = lean_mk_string_unchecked("null", 4, 4);
x_89 = l_Lean_Name_mkStr1(x_88);
x_90 = l_Array_mkArray0(lean_box(0));
lean_inc(x_89);
lean_inc(x_78);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_78);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_93 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_92);
x_94 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_78);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_94);
lean_ctor_set(x_28, 0, x_78);
lean_inc(x_78);
x_95 = l_Lean_Syntax_node2(x_78, x_93, x_28, x_33);
lean_inc(x_78);
x_96 = l_Lean_Syntax_node1(x_78, x_89, x_95);
x_97 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_78);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_78);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_87);
lean_inc(x_78);
x_99 = l_Lean_Syntax_node5(x_78, x_85, x_87, x_91, x_96, x_98, x_76);
lean_inc(x_78);
x_100 = l_Lean_Syntax_node1(x_78, x_83, x_99);
x_101 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_78);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_78);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Syntax_node4(x_78, x_80, x_81, x_100, x_102, x_87);
x_104 = l_Lean_Elab_Term_elabTerm(x_103, x_2, x_21, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_7);
return x_104;
}
}
else
{
uint8_t x_105; 
lean_free_object(x_28);
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
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_32);
if (x_105 == 0)
{
return x_32;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_32, 0);
x_107 = lean_ctor_get(x_32, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_32);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_28, 0);
x_110 = lean_ctor_get(x_28, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_111 = l_Lean_Elab_Term_exprToSyntax(x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_get(x_8, x_113);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = lean_mk_string_unchecked("this", 4, 4);
x_118 = l_Lean_Name_mkStr1(x_117);
x_119 = lean_box(0);
x_120 = lean_ctor_get(x_7, 5);
lean_inc(x_120);
x_121 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_122 = lean_unbox(x_119);
x_123 = l_Lean_SourceInfo_fromRef(x_120, x_122);
lean_dec(x_120);
x_124 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_124);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_125 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_124);
lean_inc(x_123);
if (lean_is_scalar(x_116)) {
 x_126 = lean_alloc_ctor(2, 2, 0);
} else {
 x_126 = x_116;
 lean_ctor_set_tag(x_126, 2);
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_128 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_127);
x_129 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_130 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_129);
x_131 = lean_unbox(x_119);
x_132 = l_Lean_mkIdentFrom(x_1, x_118, x_131);
lean_dec(x_1);
x_133 = lean_mk_string_unchecked("null", 4, 4);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = l_Array_mkArray0(lean_box(0));
lean_inc(x_134);
lean_inc(x_123);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_123);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_138 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_137);
x_139 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_123);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_123);
x_141 = l_Lean_Syntax_node2(x_123, x_138, x_140, x_112);
lean_inc(x_123);
x_142 = l_Lean_Syntax_node1(x_123, x_134, x_141);
x_143 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_123);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_132);
lean_inc(x_123);
x_145 = l_Lean_Syntax_node5(x_123, x_130, x_132, x_136, x_142, x_144, x_121);
lean_inc(x_123);
x_146 = l_Lean_Syntax_node1(x_123, x_128, x_145);
x_147 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_123);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_123);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_Syntax_node4(x_123, x_125, x_126, x_146, x_148, x_132);
x_150 = l_Lean_Elab_Term_elabTerm(x_149, x_2, x_21, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_115);
lean_dec(x_7);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
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
lean_dec(x_1);
x_151 = lean_ctor_get(x_111, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_111, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_153 = x_111;
} else {
 lean_dec_ref(x_111);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
else
{
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
lean_dec(x_1);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabShow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("show", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabShow", 8, 8);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabShow), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabShow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabShow", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(89u);
x_8 = lean_unsigned_to_nat(43u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(122u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(47u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(55u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandHave(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Parser", 6, 6);
x_52 = lean_mk_string_unchecked("Term", 4, 4);
x_53 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
lean_inc(x_1);
x_55 = l_Lean_Syntax_isOfKind(x_1, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_56 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = l_Lean_Syntax_getArg(x_1, x_57);
x_59 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_60 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_59);
lean_inc(x_58);
x_61 = l_Lean_Syntax_isOfKind(x_58, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_62 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_88; 
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getArg(x_58, x_63);
lean_dec(x_58);
x_65 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_66 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_65);
lean_inc(x_64);
x_88 = l_Lean_Syntax_isOfKind(x_64, x_66);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_110; 
lean_dec(x_66);
x_89 = lean_mk_string_unchecked("haveEqnsDecl", 12, 12);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_90 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_89);
lean_inc(x_64);
x_110 = l_Lean_Syntax_isOfKind(x_64, x_90);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_90);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
x_111 = lean_mk_string_unchecked("letPatDecl", 10, 10);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_112 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_111);
lean_inc(x_64);
x_113 = l_Lean_Syntax_isOfKind(x_64, x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_112);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_114 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_114;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lean_Syntax_getArg(x_64, x_57);
x_116 = l_Lean_Syntax_matchesNull(x_115, x_63);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_117 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_118 = l_Lean_Syntax_getArg(x_64, x_63);
x_168 = lean_unsigned_to_nat(2u);
x_169 = l_Lean_Syntax_getArg(x_64, x_168);
x_170 = l_Lean_Syntax_isNone(x_169);
if (x_170 == 0)
{
uint8_t x_171; 
lean_inc(x_169);
x_171 = l_Lean_Syntax_matchesNull(x_169, x_57);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_118);
lean_dec(x_112);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_172 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = l_Lean_Syntax_getArg(x_169, x_63);
lean_dec(x_169);
x_174 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_175 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_174);
lean_inc(x_173);
x_176 = l_Lean_Syntax_isOfKind(x_173, x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_173);
lean_dec(x_118);
lean_dec(x_112);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_177 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Lean_Syntax_getArg(x_173, x_57);
lean_dec(x_173);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_141 = x_179;
x_142 = x_2;
x_143 = x_3;
goto block_167;
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_169);
x_180 = lean_box(0);
x_141 = x_180;
x_142 = x_2;
x_143 = x_3;
goto block_167;
}
block_140:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = l_Array_append(lean_box(0), x_122, x_129);
lean_dec(x_129);
lean_inc(x_128);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_126);
lean_ctor_set(x_131, 2, x_130);
x_132 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_128);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_128);
x_134 = l_Lean_Syntax_node5(x_128, x_112, x_118, x_127, x_131, x_133, x_124);
lean_inc(x_128);
x_135 = l_Lean_Syntax_node1(x_128, x_121, x_134);
x_136 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_128);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Syntax_node4(x_128, x_125, x_120, x_135, x_137, x_123);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
return x_139;
}
block_167:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_unsigned_to_nat(4u);
x_146 = l_Lean_Syntax_getArg(x_64, x_145);
lean_dec(x_64);
x_147 = l_Lean_Syntax_getArg(x_1, x_144);
lean_dec(x_1);
x_148 = lean_ctor_get(x_142, 5);
x_149 = l_Lean_SourceInfo_fromRef(x_148, x_110);
x_150 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_150);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_151 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_150);
lean_inc(x_149);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_154 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_153);
x_155 = lean_mk_string_unchecked("null", 4, 4);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = l_Array_mkArray0(lean_box(0));
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_149);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_157);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_159; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_159 = l_Array_empty(lean_box(0));
x_119 = x_143;
x_120 = x_152;
x_121 = x_154;
x_122 = x_157;
x_123 = x_147;
x_124 = x_146;
x_125 = x_151;
x_126 = x_156;
x_127 = x_158;
x_128 = x_149;
x_129 = x_159;
goto block_140;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_141, 0);
lean_inc(x_160);
lean_dec(x_141);
x_161 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_162 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_161);
x_163 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_149);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_149);
x_165 = l_Lean_Syntax_node2(x_149, x_162, x_164, x_160);
x_166 = l_Array_mkArray1___redArg(x_165);
x_119 = x_143;
x_120 = x_152;
x_121 = x_154;
x_122 = x_157;
x_123 = x_147;
x_124 = x_146;
x_125 = x_151;
x_126 = x_156;
x_127 = x_158;
x_128 = x_149;
x_129 = x_166;
goto block_140;
}
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = l_Lean_Syntax_getArg(x_64, x_63);
x_182 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_183 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_182);
lean_inc(x_181);
x_184 = l_Lean_Syntax_isOfKind(x_181, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_183);
lean_dec(x_181);
lean_dec(x_90);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_185 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_186 = l_Lean_Syntax_getArg(x_181, x_63);
lean_dec(x_181);
x_208 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_209 = l_Lean_Name_mkStr1(x_208);
lean_inc(x_186);
x_210 = l_Lean_Syntax_isOfKind(x_186, x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_183);
lean_dec(x_90);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
x_211 = lean_mk_string_unchecked("ident", 5, 5);
x_212 = l_Lean_Name_mkStr1(x_211);
lean_inc(x_186);
x_213 = l_Lean_Syntax_isOfKind(x_186, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_215 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_214);
lean_inc(x_186);
x_216 = l_Lean_Syntax_isOfKind(x_186, x_215);
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_215);
lean_dec(x_186);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_217 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_218 = l_Lean_Syntax_getArg(x_64, x_57);
x_254 = lean_unsigned_to_nat(2u);
x_255 = l_Lean_Syntax_getArg(x_64, x_254);
x_256 = l_Lean_Syntax_isNone(x_255);
if (x_256 == 0)
{
uint8_t x_257; 
lean_inc(x_255);
x_257 = l_Lean_Syntax_matchesNull(x_255, x_57);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec(x_255);
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_186);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_258 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_259 = l_Lean_Syntax_getArg(x_255, x_63);
lean_dec(x_255);
x_260 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_261 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_260);
lean_inc(x_259);
x_262 = l_Lean_Syntax_isOfKind(x_259, x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_259);
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_186);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_263 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = l_Lean_Syntax_getArg(x_259, x_57);
lean_dec(x_259);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_219 = x_265;
x_220 = x_2;
x_221 = x_3;
goto block_253;
}
}
}
else
{
lean_object* x_266; 
lean_dec(x_255);
x_266 = lean_box(0);
x_219 = x_266;
x_220 = x_2;
x_221 = x_3;
goto block_253;
}
block_253:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_222 = lean_unsigned_to_nat(3u);
x_223 = l_Lean_Syntax_getArg(x_64, x_222);
lean_dec(x_64);
x_224 = l_Lean_Syntax_getArg(x_1, x_222);
lean_dec(x_1);
x_225 = l_Lean_Syntax_getArgs(x_218);
lean_dec(x_218);
x_226 = l_Lean_Syntax_getArg(x_186, x_63);
lean_dec(x_186);
x_227 = lean_ctor_get(x_220, 5);
x_228 = l_Lean_SourceInfo_fromRef(x_227, x_213);
x_229 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_229);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_230 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_229);
lean_inc(x_228);
x_231 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_233 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_232);
x_234 = lean_mk_string_unchecked("letEqnsDecl", 11, 11);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_235 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_234);
x_236 = l_Lean_SourceInfo_fromRef(x_226, x_61);
lean_dec(x_226);
x_237 = lean_mk_string_unchecked("_", 1, 1);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_228);
x_239 = l_Lean_Syntax_node1(x_228, x_215, x_238);
x_240 = lean_mk_string_unchecked("null", 4, 4);
x_241 = l_Lean_Name_mkStr1(x_240);
x_242 = l_Array_mkArray0(lean_box(0));
lean_inc(x_242);
x_243 = l_Array_append(lean_box(0), x_242, x_225);
lean_dec(x_225);
lean_inc(x_241);
lean_inc(x_228);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_228);
lean_ctor_set(x_244, 1, x_241);
lean_ctor_set(x_244, 2, x_243);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_245; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_245 = l_Array_empty(lean_box(0));
x_28 = x_228;
x_29 = x_230;
x_30 = x_223;
x_31 = x_244;
x_32 = x_224;
x_33 = x_235;
x_34 = x_221;
x_35 = x_241;
x_36 = x_231;
x_37 = x_233;
x_38 = x_239;
x_39 = x_242;
x_40 = x_245;
goto block_49;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_219, 0);
lean_inc(x_246);
lean_dec(x_219);
x_247 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_248 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_247);
x_249 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_228);
x_250 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_250, 0, x_228);
lean_ctor_set(x_250, 1, x_249);
lean_inc(x_228);
x_251 = l_Lean_Syntax_node2(x_228, x_248, x_250, x_246);
x_252 = l_Array_mkArray1___redArg(x_251);
x_28 = x_228;
x_29 = x_230;
x_30 = x_223;
x_31 = x_244;
x_32 = x_224;
x_33 = x_235;
x_34 = x_221;
x_35 = x_241;
x_36 = x_231;
x_37 = x_233;
x_38 = x_239;
x_39 = x_242;
x_40 = x_252;
goto block_49;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_267 = l_Lean_Syntax_getArg(x_64, x_57);
x_298 = lean_unsigned_to_nat(2u);
x_299 = l_Lean_Syntax_getArg(x_64, x_298);
x_300 = l_Lean_Syntax_isNone(x_299);
if (x_300 == 0)
{
uint8_t x_301; 
lean_inc(x_299);
x_301 = l_Lean_Syntax_matchesNull(x_299, x_57);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_299);
lean_dec(x_267);
lean_dec(x_186);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_302 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = l_Lean_Syntax_getArg(x_299, x_63);
lean_dec(x_299);
x_304 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_305 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_304);
lean_inc(x_303);
x_306 = l_Lean_Syntax_isOfKind(x_303, x_305);
lean_dec(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_303);
lean_dec(x_267);
lean_dec(x_186);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_307 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = l_Lean_Syntax_getArg(x_303, x_57);
lean_dec(x_303);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_268 = x_309;
x_269 = x_2;
x_270 = x_3;
goto block_297;
}
}
}
else
{
lean_object* x_310; 
lean_dec(x_299);
x_310 = lean_box(0);
x_268 = x_310;
x_269 = x_2;
x_270 = x_3;
goto block_297;
}
block_297:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_271 = lean_unsigned_to_nat(3u);
x_272 = l_Lean_Syntax_getArg(x_64, x_271);
lean_dec(x_64);
x_273 = l_Lean_Syntax_getArg(x_1, x_271);
lean_dec(x_1);
x_274 = l_Lean_Syntax_getArgs(x_267);
lean_dec(x_267);
x_275 = lean_ctor_get(x_269, 5);
x_276 = l_Lean_SourceInfo_fromRef(x_275, x_210);
x_277 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_277);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_278 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_277);
lean_inc(x_276);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_281 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_280);
x_282 = lean_mk_string_unchecked("letEqnsDecl", 11, 11);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_283 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_282);
x_284 = lean_mk_string_unchecked("null", 4, 4);
x_285 = l_Lean_Name_mkStr1(x_284);
x_286 = l_Array_mkArray0(lean_box(0));
lean_inc(x_286);
x_287 = l_Array_append(lean_box(0), x_286, x_274);
lean_dec(x_274);
lean_inc(x_285);
lean_inc(x_276);
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_276);
lean_ctor_set(x_288, 1, x_285);
lean_ctor_set(x_288, 2, x_287);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_289; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_289 = l_Array_empty(lean_box(0));
x_187 = x_270;
x_188 = x_272;
x_189 = x_288;
x_190 = x_286;
x_191 = x_278;
x_192 = x_281;
x_193 = x_285;
x_194 = x_279;
x_195 = x_283;
x_196 = x_276;
x_197 = x_273;
x_198 = x_289;
goto block_207;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_290 = lean_ctor_get(x_268, 0);
lean_inc(x_290);
lean_dec(x_268);
x_291 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_292 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_291);
x_293 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_276);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_276);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_276);
x_295 = l_Lean_Syntax_node2(x_276, x_292, x_294, x_290);
x_296 = l_Array_mkArray1___redArg(x_295);
x_187 = x_270;
x_188 = x_272;
x_189 = x_288;
x_190 = x_286;
x_191 = x_278;
x_192 = x_281;
x_193 = x_285;
x_194 = x_279;
x_195 = x_283;
x_196 = x_276;
x_197 = x_273;
x_198 = x_296;
goto block_207;
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_311 = l_Lean_Syntax_getArg(x_64, x_57);
x_340 = lean_unsigned_to_nat(2u);
x_341 = l_Lean_Syntax_getArg(x_64, x_340);
x_342 = l_Lean_Syntax_isNone(x_341);
if (x_342 == 0)
{
uint8_t x_343; 
lean_inc(x_341);
x_343 = l_Lean_Syntax_matchesNull(x_341, x_57);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_341);
lean_dec(x_311);
lean_dec(x_186);
lean_dec(x_183);
lean_dec(x_90);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_344 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = l_Lean_Syntax_getArg(x_341, x_63);
lean_dec(x_341);
x_346 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_347 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_346);
lean_inc(x_345);
x_348 = l_Lean_Syntax_isOfKind(x_345, x_347);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
lean_dec(x_345);
lean_dec(x_311);
lean_dec(x_186);
lean_dec(x_183);
lean_dec(x_90);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_349 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = l_Lean_Syntax_getArg(x_345, x_57);
lean_dec(x_345);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
x_312 = x_351;
x_313 = x_2;
x_314 = x_3;
goto block_339;
}
}
}
else
{
lean_object* x_352; 
lean_dec(x_341);
x_352 = lean_box(0);
x_312 = x_352;
x_313 = x_2;
x_314 = x_3;
goto block_339;
}
block_339:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_315 = lean_unsigned_to_nat(3u);
x_316 = l_Lean_Syntax_getArg(x_64, x_315);
lean_dec(x_64);
x_317 = l_Lean_Syntax_getArg(x_1, x_315);
lean_dec(x_1);
x_318 = l_Lean_Syntax_getArgs(x_311);
lean_dec(x_311);
x_319 = lean_ctor_get(x_313, 5);
x_320 = l_Lean_SourceInfo_fromRef(x_319, x_88);
lean_inc(x_320);
x_321 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_53);
x_322 = lean_mk_string_unchecked("this", 4, 4);
x_323 = l_Lean_Name_mkStr1(x_322);
x_324 = l_Lean_HygieneInfo_mkIdent(x_186, x_323, x_61);
lean_dec(x_186);
lean_inc(x_320);
x_325 = l_Lean_Syntax_node1(x_320, x_183, x_324);
x_326 = lean_mk_string_unchecked("null", 4, 4);
x_327 = l_Lean_Name_mkStr1(x_326);
x_328 = l_Array_mkArray0(lean_box(0));
lean_inc(x_328);
x_329 = l_Array_append(lean_box(0), x_328, x_318);
lean_dec(x_318);
lean_inc(x_327);
lean_inc(x_320);
x_330 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_330, 0, x_320);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_329);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_331; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_331 = l_Array_empty(lean_box(0));
x_91 = x_314;
x_92 = x_321;
x_93 = x_320;
x_94 = x_328;
x_95 = x_330;
x_96 = x_316;
x_97 = x_325;
x_98 = x_317;
x_99 = x_327;
x_100 = x_331;
goto block_109;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_332 = lean_ctor_get(x_312, 0);
lean_inc(x_332);
lean_dec(x_312);
x_333 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_334 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_333);
x_335 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_320);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_320);
lean_ctor_set(x_336, 1, x_335);
lean_inc(x_320);
x_337 = l_Lean_Syntax_node2(x_320, x_334, x_336, x_332);
x_338 = l_Array_mkArray1___redArg(x_337);
x_91 = x_314;
x_92 = x_321;
x_93 = x_320;
x_94 = x_328;
x_95 = x_330;
x_96 = x_316;
x_97 = x_325;
x_98 = x_317;
x_99 = x_327;
x_100 = x_338;
goto block_109;
}
}
}
block_207:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = l_Array_append(lean_box(0), x_190, x_198);
lean_dec(x_198);
lean_inc(x_196);
x_200 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_193);
lean_ctor_set(x_200, 2, x_199);
lean_inc(x_196);
x_201 = l_Lean_Syntax_node4(x_196, x_195, x_186, x_189, x_200, x_188);
lean_inc(x_196);
x_202 = l_Lean_Syntax_node1(x_196, x_192, x_201);
x_203 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_196);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_196);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Syntax_node4(x_196, x_191, x_194, x_202, x_204, x_197);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_187);
return x_206;
}
}
}
block_109:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = l_Array_append(lean_box(0), x_94, x_100);
lean_dec(x_100);
lean_inc(x_93);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_101);
lean_inc(x_93);
x_103 = l_Lean_Syntax_node4(x_93, x_90, x_97, x_95, x_102, x_96);
lean_inc(x_93);
x_104 = l_Lean_Syntax_node1(x_93, x_60, x_103);
x_105 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_93);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_93);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Syntax_node4(x_93, x_54, x_92, x_104, x_106, x_98);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_91);
return x_108;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_353 = l_Lean_Syntax_getArg(x_64, x_63);
x_354 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_355 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_354);
lean_inc(x_353);
x_356 = l_Lean_Syntax_isOfKind(x_353, x_355);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_357 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_358 = l_Lean_Syntax_getArg(x_353, x_63);
lean_dec(x_353);
x_382 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_383 = l_Lean_Name_mkStr1(x_382);
lean_inc(x_358);
x_384 = l_Lean_Syntax_isOfKind(x_358, x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; 
lean_dec(x_355);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
x_385 = lean_mk_string_unchecked("ident", 5, 5);
x_386 = l_Lean_Name_mkStr1(x_385);
lean_inc(x_358);
x_387 = l_Lean_Syntax_isOfKind(x_358, x_386);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_388 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_389 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_388);
lean_inc(x_358);
x_390 = l_Lean_Syntax_isOfKind(x_358, x_389);
if (x_390 == 0)
{
lean_object* x_391; 
lean_dec(x_389);
lean_dec(x_358);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_391 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_392 = l_Lean_Syntax_getArg(x_64, x_57);
x_429 = lean_unsigned_to_nat(2u);
x_430 = l_Lean_Syntax_getArg(x_64, x_429);
x_431 = l_Lean_Syntax_isNone(x_430);
if (x_431 == 0)
{
uint8_t x_432; 
lean_inc(x_430);
x_432 = l_Lean_Syntax_matchesNull(x_430, x_57);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_430);
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_358);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_433 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_434 = l_Lean_Syntax_getArg(x_430, x_63);
lean_dec(x_430);
x_435 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_436 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_435);
lean_inc(x_434);
x_437 = l_Lean_Syntax_isOfKind(x_434, x_436);
lean_dec(x_436);
if (x_437 == 0)
{
lean_object* x_438; 
lean_dec(x_434);
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_358);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_438 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = l_Lean_Syntax_getArg(x_434, x_57);
lean_dec(x_434);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_393 = x_440;
x_394 = x_2;
x_395 = x_3;
goto block_428;
}
}
}
else
{
lean_object* x_441; 
lean_dec(x_430);
x_441 = lean_box(0);
x_393 = x_441;
x_394 = x_2;
x_395 = x_3;
goto block_428;
}
block_428:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_396 = lean_unsigned_to_nat(3u);
x_397 = lean_unsigned_to_nat(4u);
x_398 = l_Lean_Syntax_getArg(x_64, x_397);
lean_dec(x_64);
x_399 = l_Lean_Syntax_getArg(x_1, x_396);
lean_dec(x_1);
x_400 = l_Lean_Syntax_getArgs(x_392);
lean_dec(x_392);
x_401 = l_Lean_Syntax_getArg(x_358, x_63);
lean_dec(x_358);
x_402 = lean_ctor_get(x_394, 5);
x_403 = l_Lean_SourceInfo_fromRef(x_402, x_387);
x_404 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_404);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_405 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_404);
lean_inc(x_403);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
x_407 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_408 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_407);
x_409 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_410 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_409);
x_411 = l_Lean_SourceInfo_fromRef(x_401, x_61);
lean_dec(x_401);
x_412 = lean_mk_string_unchecked("_", 1, 1);
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
lean_inc(x_403);
x_414 = l_Lean_Syntax_node1(x_403, x_389, x_413);
x_415 = lean_mk_string_unchecked("null", 4, 4);
x_416 = l_Lean_Name_mkStr1(x_415);
x_417 = l_Array_mkArray0(lean_box(0));
lean_inc(x_417);
x_418 = l_Array_append(lean_box(0), x_417, x_400);
lean_dec(x_400);
lean_inc(x_416);
lean_inc(x_403);
x_419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_419, 0, x_403);
lean_ctor_set(x_419, 1, x_416);
lean_ctor_set(x_419, 2, x_418);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_420; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_420 = l_Array_empty(lean_box(0));
x_4 = x_419;
x_5 = x_416;
x_6 = x_406;
x_7 = x_405;
x_8 = x_395;
x_9 = x_398;
x_10 = x_410;
x_11 = x_417;
x_12 = x_408;
x_13 = x_414;
x_14 = x_399;
x_15 = x_403;
x_16 = x_420;
goto block_27;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_ctor_get(x_393, 0);
lean_inc(x_421);
lean_dec(x_393);
x_422 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_423 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_422);
x_424 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_403);
x_425 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_425, 0, x_403);
lean_ctor_set(x_425, 1, x_424);
lean_inc(x_403);
x_426 = l_Lean_Syntax_node2(x_403, x_423, x_425, x_421);
x_427 = l_Array_mkArray1___redArg(x_426);
x_4 = x_419;
x_5 = x_416;
x_6 = x_406;
x_7 = x_405;
x_8 = x_395;
x_9 = x_398;
x_10 = x_410;
x_11 = x_417;
x_12 = x_408;
x_13 = x_414;
x_14 = x_399;
x_15 = x_403;
x_16 = x_427;
goto block_27;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_442 = l_Lean_Syntax_getArg(x_64, x_57);
x_474 = lean_unsigned_to_nat(2u);
x_475 = l_Lean_Syntax_getArg(x_64, x_474);
x_476 = l_Lean_Syntax_isNone(x_475);
if (x_476 == 0)
{
uint8_t x_477; 
lean_inc(x_475);
x_477 = l_Lean_Syntax_matchesNull(x_475, x_57);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_475);
lean_dec(x_442);
lean_dec(x_358);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_478 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_479 = l_Lean_Syntax_getArg(x_475, x_63);
lean_dec(x_475);
x_480 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_481 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_480);
lean_inc(x_479);
x_482 = l_Lean_Syntax_isOfKind(x_479, x_481);
lean_dec(x_481);
if (x_482 == 0)
{
lean_object* x_483; 
lean_dec(x_479);
lean_dec(x_442);
lean_dec(x_358);
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_483 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; 
x_484 = l_Lean_Syntax_getArg(x_479, x_57);
lean_dec(x_479);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_443 = x_485;
x_444 = x_2;
x_445 = x_3;
goto block_473;
}
}
}
else
{
lean_object* x_486; 
lean_dec(x_475);
x_486 = lean_box(0);
x_443 = x_486;
x_444 = x_2;
x_445 = x_3;
goto block_473;
}
block_473:
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_446 = lean_unsigned_to_nat(3u);
x_447 = lean_unsigned_to_nat(4u);
x_448 = l_Lean_Syntax_getArg(x_64, x_447);
lean_dec(x_64);
x_449 = l_Lean_Syntax_getArg(x_1, x_446);
lean_dec(x_1);
x_450 = l_Lean_Syntax_getArgs(x_442);
lean_dec(x_442);
x_451 = lean_ctor_get(x_444, 5);
x_452 = l_Lean_SourceInfo_fromRef(x_451, x_384);
x_453 = lean_mk_string_unchecked("let_fun", 7, 7);
lean_inc(x_453);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_454 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_453);
lean_inc(x_452);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_453);
x_456 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_457 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_456);
x_458 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_459 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_458);
x_460 = lean_mk_string_unchecked("null", 4, 4);
x_461 = l_Lean_Name_mkStr1(x_460);
x_462 = l_Array_mkArray0(lean_box(0));
lean_inc(x_462);
x_463 = l_Array_append(lean_box(0), x_462, x_450);
lean_dec(x_450);
lean_inc(x_461);
lean_inc(x_452);
x_464 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_464, 0, x_452);
lean_ctor_set(x_464, 1, x_461);
lean_ctor_set(x_464, 2, x_463);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_465; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_465 = l_Array_empty(lean_box(0));
x_359 = x_454;
x_360 = x_448;
x_361 = x_445;
x_362 = x_449;
x_363 = x_457;
x_364 = x_452;
x_365 = x_455;
x_366 = x_459;
x_367 = x_462;
x_368 = x_461;
x_369 = x_464;
x_370 = x_465;
goto block_381;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_443, 0);
lean_inc(x_466);
lean_dec(x_443);
x_467 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_468 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_467);
x_469 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_452);
x_470 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_470, 0, x_452);
lean_ctor_set(x_470, 1, x_469);
lean_inc(x_452);
x_471 = l_Lean_Syntax_node2(x_452, x_468, x_470, x_466);
x_472 = l_Array_mkArray1___redArg(x_471);
x_359 = x_454;
x_360 = x_448;
x_361 = x_445;
x_362 = x_449;
x_363 = x_457;
x_364 = x_452;
x_365 = x_455;
x_366 = x_459;
x_367 = x_462;
x_368 = x_461;
x_369 = x_464;
x_370 = x_472;
goto block_381;
}
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_487 = l_Lean_Syntax_getArg(x_64, x_57);
x_519 = lean_unsigned_to_nat(2u);
x_520 = l_Lean_Syntax_getArg(x_64, x_519);
x_521 = l_Lean_Syntax_isNone(x_520);
if (x_521 == 0)
{
uint8_t x_522; 
lean_inc(x_520);
x_522 = l_Lean_Syntax_matchesNull(x_520, x_57);
if (x_522 == 0)
{
lean_object* x_523; 
lean_dec(x_520);
lean_dec(x_487);
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_523 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_523;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_524 = l_Lean_Syntax_getArg(x_520, x_63);
lean_dec(x_520);
x_525 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_526 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_525);
lean_inc(x_524);
x_527 = l_Lean_Syntax_isOfKind(x_524, x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; 
lean_dec(x_524);
lean_dec(x_487);
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_528 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; 
x_529 = l_Lean_Syntax_getArg(x_524, x_57);
lean_dec(x_524);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_529);
x_488 = x_530;
x_489 = x_2;
x_490 = x_3;
goto block_518;
}
}
}
else
{
lean_object* x_531; 
lean_dec(x_520);
x_531 = lean_box(0);
x_488 = x_531;
x_489 = x_2;
x_490 = x_3;
goto block_518;
}
block_518:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_491 = lean_unsigned_to_nat(3u);
x_492 = lean_unsigned_to_nat(4u);
x_493 = l_Lean_Syntax_getArg(x_64, x_492);
lean_dec(x_64);
x_494 = l_Lean_Syntax_getArg(x_1, x_491);
lean_dec(x_1);
x_495 = l_Lean_Syntax_getArgs(x_487);
lean_dec(x_487);
x_496 = lean_ctor_get(x_489, 5);
x_497 = lean_box(0);
x_498 = lean_unbox(x_497);
x_499 = l_Lean_SourceInfo_fromRef(x_496, x_498);
lean_inc(x_499);
x_500 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_53);
x_501 = lean_mk_string_unchecked("this", 4, 4);
x_502 = l_Lean_Name_mkStr1(x_501);
x_503 = l_Lean_HygieneInfo_mkIdent(x_358, x_502, x_61);
lean_dec(x_358);
lean_inc(x_499);
x_504 = l_Lean_Syntax_node1(x_499, x_355, x_503);
x_505 = lean_mk_string_unchecked("null", 4, 4);
x_506 = l_Lean_Name_mkStr1(x_505);
x_507 = l_Array_mkArray0(lean_box(0));
lean_inc(x_507);
x_508 = l_Array_append(lean_box(0), x_507, x_495);
lean_dec(x_495);
lean_inc(x_506);
lean_inc(x_499);
x_509 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_509, 0, x_499);
lean_ctor_set(x_509, 1, x_506);
lean_ctor_set(x_509, 2, x_508);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_510; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_510 = l_Array_empty(lean_box(0));
x_67 = x_494;
x_68 = x_499;
x_69 = x_506;
x_70 = x_509;
x_71 = x_504;
x_72 = x_493;
x_73 = x_490;
x_74 = x_507;
x_75 = x_500;
x_76 = x_510;
goto block_87;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_511 = lean_ctor_get(x_488, 0);
lean_inc(x_511);
lean_dec(x_488);
x_512 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_513 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_512);
x_514 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_499);
x_515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_515, 0, x_499);
lean_ctor_set(x_515, 1, x_514);
lean_inc(x_499);
x_516 = l_Lean_Syntax_node2(x_499, x_513, x_515, x_511);
x_517 = l_Array_mkArray1___redArg(x_516);
x_67 = x_494;
x_68 = x_499;
x_69 = x_506;
x_70 = x_509;
x_71 = x_504;
x_72 = x_493;
x_73 = x_490;
x_74 = x_507;
x_75 = x_500;
x_76 = x_517;
goto block_87;
}
}
}
block_381:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_371 = l_Array_append(lean_box(0), x_367, x_370);
lean_dec(x_370);
lean_inc(x_364);
x_372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_372, 0, x_364);
lean_ctor_set(x_372, 1, x_368);
lean_ctor_set(x_372, 2, x_371);
x_373 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_364);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_364);
lean_ctor_set(x_374, 1, x_373);
lean_inc(x_364);
x_375 = l_Lean_Syntax_node5(x_364, x_366, x_358, x_369, x_372, x_374, x_360);
lean_inc(x_364);
x_376 = l_Lean_Syntax_node1(x_364, x_363, x_375);
x_377 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_364);
x_378 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_378, 0, x_364);
lean_ctor_set(x_378, 1, x_377);
x_379 = l_Lean_Syntax_node4(x_364, x_359, x_365, x_376, x_378, x_362);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_361);
return x_380;
}
}
}
block_87:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = l_Array_append(lean_box(0), x_74, x_76);
lean_dec(x_76);
lean_inc(x_68);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_68);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_68);
x_81 = l_Lean_Syntax_node5(x_68, x_66, x_71, x_70, x_78, x_80, x_72);
lean_inc(x_68);
x_82 = l_Lean_Syntax_node1(x_68, x_60, x_81);
x_83 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_68);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_68);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Syntax_node4(x_68, x_54, x_75, x_82, x_84, x_67);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
return x_86;
}
}
}
block_27:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = l_Array_append(lean_box(0), x_11, x_16);
lean_dec(x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_15);
x_21 = l_Lean_Syntax_node5(x_15, x_10, x_13, x_4, x_18, x_20, x_9);
lean_inc(x_15);
x_22 = l_Lean_Syntax_node1(x_15, x_12, x_21);
x_23 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_15);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Syntax_node4(x_15, x_7, x_6, x_22, x_24, x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
block_49:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = l_Array_append(lean_box(0), x_39, x_40);
lean_dec(x_40);
lean_inc(x_28);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_41);
lean_inc(x_28);
x_43 = l_Lean_Syntax_node4(x_28, x_33, x_38, x_31, x_42, x_30);
lean_inc(x_28);
x_44 = l_Lean_Syntax_node1(x_28, x_37, x_43);
x_45 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_28);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Syntax_node4(x_28, x_29, x_36, x_44, x_46, x_32);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandHave(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandHave__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandHave", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandHave_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandHave", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(124u);
x_8 = lean_unsigned_to_nat(39u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(135u);
x_11 = lean_unsigned_to_nat(78u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(53u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSuffices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("suffices", 8, 8);
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
x_13 = lean_mk_string_unchecked("sufficesDecl", 12, 12);
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
lean_dec(x_1);
x_16 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
x_19 = lean_mk_string_unchecked("group", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_23 = l_Lean_Name_mkStr1(x_22);
lean_inc(x_18);
x_24 = l_Lean_Syntax_isOfKind(x_18, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = l_Lean_Syntax_getArg(x_12, x_11);
x_27 = lean_unsigned_to_nat(2u);
x_28 = l_Lean_Syntax_getArg(x_12, x_27);
lean_dec(x_12);
x_29 = lean_mk_string_unchecked("fromTerm", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_29);
lean_inc(x_28);
x_31 = l_Lean_Syntax_isOfKind(x_28, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("byTactic'", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_32);
lean_inc(x_28);
x_34 = l_Lean_Syntax_isOfKind(x_28, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_36 = lean_unsigned_to_nat(3u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_39 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_39);
x_41 = l_Lean_Syntax_setKind(x_28, x_40);
x_42 = lean_ctor_get(x_2, 5);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_31);
x_44 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_44);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_44);
x_46 = l_Lean_SourceInfo_fromRef(x_38, x_15);
lean_dec(x_38);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_49 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_48);
x_50 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_50);
x_52 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_52);
lean_inc(x_43);
x_54 = l_Lean_Syntax_node1(x_43, x_53, x_18);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Array_mkArray0(lean_box(0));
lean_inc(x_56);
lean_inc(x_43);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_60 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_59);
x_61 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_43);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_43);
x_63 = l_Lean_Syntax_node2(x_43, x_60, x_62, x_26);
lean_inc(x_43);
x_64 = l_Lean_Syntax_node1(x_43, x_56, x_63);
x_65 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_43);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_43);
x_67 = l_Lean_Syntax_node5(x_43, x_51, x_54, x_58, x_64, x_66, x_37);
lean_inc(x_43);
x_68 = l_Lean_Syntax_node1(x_43, x_49, x_67);
x_69 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_43);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_43);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Syntax_node4(x_43, x_45, x_47, x_68, x_70, x_41);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_73 = l_Lean_Syntax_getArg(x_28, x_11);
lean_dec(x_28);
x_74 = lean_unsigned_to_nat(3u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
x_76 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_77 = lean_ctor_get(x_2, 5);
x_78 = l_Lean_SourceInfo_fromRef(x_77, x_21);
x_79 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_79);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_80 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_79);
x_81 = l_Lean_SourceInfo_fromRef(x_76, x_15);
lean_dec(x_76);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
x_83 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_83);
x_85 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_86 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_85);
x_87 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_88 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_87);
lean_inc(x_78);
x_89 = l_Lean_Syntax_node1(x_78, x_88, x_18);
x_90 = lean_mk_string_unchecked("null", 4, 4);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = l_Array_mkArray0(lean_box(0));
lean_inc(x_91);
lean_inc(x_78);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_95 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_94);
x_96 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_78);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_78);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_78);
x_98 = l_Lean_Syntax_node2(x_78, x_95, x_97, x_26);
lean_inc(x_78);
x_99 = l_Lean_Syntax_node1(x_78, x_91, x_98);
x_100 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_78);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_78);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_78);
x_102 = l_Lean_Syntax_node5(x_78, x_86, x_89, x_93, x_99, x_101, x_75);
lean_inc(x_78);
x_103 = l_Lean_Syntax_node1(x_78, x_84, x_102);
x_104 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_78);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_78);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Syntax_node4(x_78, x_80, x_82, x_103, x_105, x_73);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_3);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_109 = lean_mk_string_unchecked("ident", 5, 5);
x_110 = l_Lean_Name_mkStr1(x_109);
lean_inc(x_108);
x_111 = l_Lean_Syntax_isOfKind(x_108, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_112);
lean_inc(x_108);
x_114 = l_Lean_Syntax_isOfKind(x_108, x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_115 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = l_Lean_Syntax_getArg(x_12, x_11);
x_117 = lean_unsigned_to_nat(2u);
x_118 = l_Lean_Syntax_getArg(x_12, x_117);
lean_dec(x_12);
x_119 = lean_mk_string_unchecked("fromTerm", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_120 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_119);
lean_inc(x_118);
x_121 = l_Lean_Syntax_isOfKind(x_118, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_mk_string_unchecked("byTactic'", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_123 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_122);
lean_inc(x_118);
x_124 = l_Lean_Syntax_isOfKind(x_118, x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_125 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_126 = lean_unsigned_to_nat(3u);
x_127 = l_Lean_Syntax_getArg(x_1, x_126);
x_128 = l_Lean_Syntax_getArg(x_108, x_17);
lean_dec(x_108);
x_129 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_130 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_131 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_130);
x_132 = l_Lean_Syntax_setKind(x_118, x_131);
x_133 = lean_ctor_get(x_2, 5);
x_134 = l_Lean_SourceInfo_fromRef(x_133, x_121);
x_135 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_136 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_135);
x_137 = l_Lean_SourceInfo_fromRef(x_129, x_15);
lean_dec(x_129);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
x_139 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_140 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_139);
x_141 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_142 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_141);
x_143 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_144 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_143);
x_145 = l_Lean_SourceInfo_fromRef(x_128, x_15);
lean_dec(x_128);
x_146 = lean_mk_string_unchecked("_", 1, 1);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_134);
x_148 = l_Lean_Syntax_node1(x_134, x_113, x_147);
lean_inc(x_134);
x_149 = l_Lean_Syntax_node1(x_134, x_144, x_148);
x_150 = lean_mk_string_unchecked("null", 4, 4);
x_151 = l_Lean_Name_mkStr1(x_150);
x_152 = l_Array_mkArray0(lean_box(0));
lean_inc(x_151);
lean_inc(x_134);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_152);
x_154 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_155 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_154);
x_156 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_134);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_134);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_134);
x_158 = l_Lean_Syntax_node2(x_134, x_155, x_157, x_116);
lean_inc(x_134);
x_159 = l_Lean_Syntax_node1(x_134, x_151, x_158);
x_160 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_134);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_134);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_134);
x_162 = l_Lean_Syntax_node5(x_134, x_142, x_149, x_153, x_159, x_161, x_127);
lean_inc(x_134);
x_163 = l_Lean_Syntax_node1(x_134, x_140, x_162);
x_164 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_134);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_134);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_Syntax_node4(x_134, x_136, x_138, x_163, x_165, x_132);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_3);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_168 = l_Lean_Syntax_getArg(x_118, x_11);
lean_dec(x_118);
x_169 = lean_unsigned_to_nat(3u);
x_170 = l_Lean_Syntax_getArg(x_1, x_169);
x_171 = l_Lean_Syntax_getArg(x_108, x_17);
lean_dec(x_108);
x_172 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_173 = lean_ctor_get(x_2, 5);
x_174 = l_Lean_SourceInfo_fromRef(x_173, x_111);
x_175 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_175);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_176 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_175);
x_177 = l_Lean_SourceInfo_fromRef(x_172, x_15);
lean_dec(x_172);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
x_179 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_180 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_179);
x_181 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_182 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_181);
x_183 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_184 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_183);
x_185 = l_Lean_SourceInfo_fromRef(x_171, x_15);
lean_dec(x_171);
x_186 = lean_mk_string_unchecked("_", 1, 1);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
lean_inc(x_174);
x_188 = l_Lean_Syntax_node1(x_174, x_113, x_187);
lean_inc(x_174);
x_189 = l_Lean_Syntax_node1(x_174, x_184, x_188);
x_190 = lean_mk_string_unchecked("null", 4, 4);
x_191 = l_Lean_Name_mkStr1(x_190);
x_192 = l_Array_mkArray0(lean_box(0));
lean_inc(x_191);
lean_inc(x_174);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_174);
lean_ctor_set(x_193, 1, x_191);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_195 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_194);
x_196 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_174);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_174);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_174);
x_198 = l_Lean_Syntax_node2(x_174, x_195, x_197, x_116);
lean_inc(x_174);
x_199 = l_Lean_Syntax_node1(x_174, x_191, x_198);
x_200 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_174);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_174);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_174);
x_202 = l_Lean_Syntax_node5(x_174, x_182, x_189, x_193, x_199, x_201, x_170);
lean_inc(x_174);
x_203 = l_Lean_Syntax_node1(x_174, x_180, x_202);
x_204 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_174);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_174);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_Syntax_node4(x_174, x_176, x_178, x_203, x_205, x_168);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_3);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_208 = l_Lean_Syntax_getArg(x_12, x_11);
x_209 = lean_unsigned_to_nat(2u);
x_210 = l_Lean_Syntax_getArg(x_12, x_209);
lean_dec(x_12);
x_211 = lean_mk_string_unchecked("fromTerm", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_212 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_211);
lean_inc(x_210);
x_213 = l_Lean_Syntax_isOfKind(x_210, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_mk_string_unchecked("byTactic'", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_215 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_214);
lean_inc(x_210);
x_216 = l_Lean_Syntax_isOfKind(x_210, x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_217 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_218 = lean_unsigned_to_nat(3u);
x_219 = l_Lean_Syntax_getArg(x_1, x_218);
x_220 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_221 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_222 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_221);
x_223 = l_Lean_Syntax_setKind(x_210, x_222);
x_224 = lean_ctor_get(x_2, 5);
x_225 = l_Lean_SourceInfo_fromRef(x_224, x_213);
x_226 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_226);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_227 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_226);
x_228 = l_Lean_SourceInfo_fromRef(x_220, x_15);
lean_dec(x_220);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
x_230 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_231 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_230);
x_232 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_233 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_232);
x_234 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_235 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_234);
lean_inc(x_225);
x_236 = l_Lean_Syntax_node1(x_225, x_235, x_108);
x_237 = lean_mk_string_unchecked("null", 4, 4);
x_238 = l_Lean_Name_mkStr1(x_237);
x_239 = l_Array_mkArray0(lean_box(0));
lean_inc(x_238);
lean_inc(x_225);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_225);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_240, 2, x_239);
x_241 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_242 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_241);
x_243 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_225);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_225);
lean_ctor_set(x_244, 1, x_243);
lean_inc(x_225);
x_245 = l_Lean_Syntax_node2(x_225, x_242, x_244, x_208);
lean_inc(x_225);
x_246 = l_Lean_Syntax_node1(x_225, x_238, x_245);
x_247 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_225);
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_225);
lean_ctor_set(x_248, 1, x_247);
lean_inc(x_225);
x_249 = l_Lean_Syntax_node5(x_225, x_233, x_236, x_240, x_246, x_248, x_219);
lean_inc(x_225);
x_250 = l_Lean_Syntax_node1(x_225, x_231, x_249);
x_251 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_225);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_225);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_Syntax_node4(x_225, x_227, x_229, x_250, x_252, x_223);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_3);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_255 = l_Lean_Syntax_getArg(x_210, x_11);
lean_dec(x_210);
x_256 = lean_unsigned_to_nat(3u);
x_257 = l_Lean_Syntax_getArg(x_1, x_256);
x_258 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_259 = lean_ctor_get(x_2, 5);
x_260 = lean_box(0);
x_261 = lean_unbox(x_260);
x_262 = l_Lean_SourceInfo_fromRef(x_259, x_261);
x_263 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_263);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_264 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_263);
x_265 = l_Lean_SourceInfo_fromRef(x_258, x_15);
lean_dec(x_258);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
x_267 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_268 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_267);
x_269 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_270 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_269);
x_271 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_272 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_271);
lean_inc(x_262);
x_273 = l_Lean_Syntax_node1(x_262, x_272, x_108);
x_274 = lean_mk_string_unchecked("null", 4, 4);
x_275 = l_Lean_Name_mkStr1(x_274);
x_276 = l_Array_mkArray0(lean_box(0));
lean_inc(x_275);
lean_inc(x_262);
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_262);
lean_ctor_set(x_277, 1, x_275);
lean_ctor_set(x_277, 2, x_276);
x_278 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_279 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_278);
x_280 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_262);
x_281 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_281, 0, x_262);
lean_ctor_set(x_281, 1, x_280);
lean_inc(x_262);
x_282 = l_Lean_Syntax_node2(x_262, x_279, x_281, x_208);
lean_inc(x_262);
x_283 = l_Lean_Syntax_node1(x_262, x_275, x_282);
x_284 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_262);
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_262);
lean_ctor_set(x_285, 1, x_284);
lean_inc(x_262);
x_286 = l_Lean_Syntax_node5(x_262, x_270, x_273, x_277, x_283, x_285, x_257);
lean_inc(x_262);
x_287 = l_Lean_Syntax_node1(x_262, x_268, x_286);
x_288 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_262);
x_289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_289, 0, x_262);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_Syntax_node4(x_262, x_264, x_266, x_287, x_289, x_255);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_3);
return x_291;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSuffices(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("suffices", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandSuffices", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandSuffices", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(137u);
x_8 = lean_unsigned_to_nat(43u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(144u);
x_11 = lean_unsigned_to_nat(95u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(47u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(61u);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0(x_5);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_13; 
x_5 = lean_box(1);
x_13 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
x_6 = x_4;
goto block_12;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_LocalDecl_isAuxDecl(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_unbox(x_5);
return x_16;
}
else
{
x_6 = x_4;
goto block_12;
}
}
block_12:
{
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
uint8_t x_11; 
x_11 = lean_unbox(x_5);
return x_11;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0(lean_object* x_1) {
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
x_8 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0(x_2, x_6, x_7);
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
x_15 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1(x_9, x_13, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0(x_2);
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
x_10 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1(x_4, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("invalid `leading_parser` macro, unexpected declaration name", 59, 59);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_4, x_10);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_mk_string_unchecked("invalid `leading_parser` macro, it must be used in definitions", 62, 62);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
lean_dec(x_8);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
lean_inc(x_100);
x_102 = l_Lean_extractMacroScopes(x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
switch (lean_obj_tag(x_103)) {
case 0:
{
uint8_t x_104; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_102, 0, x_106);
x_107 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_8);
lean_dec(x_102);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_102, 1);
x_109 = lean_ctor_get(x_102, 2);
x_110 = lean_ctor_get(x_102, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_110);
x_113 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_8);
lean_dec(x_112);
return x_113;
}
}
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_218; lean_object* x_219; 
lean_dec(x_102);
lean_dec(x_4);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
lean_dec(x_103);
x_218 = lean_box(0);
lean_inc(x_100);
x_219 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_218, x_100);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = l_Lean_quoteNameMk(x_100);
x_115 = x_220;
goto block_217;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_100);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_mk_string_unchecked("Lean", 4, 4);
x_223 = lean_mk_string_unchecked("Parser", 6, 6);
x_224 = lean_mk_string_unchecked("Term", 4, 4);
x_225 = lean_mk_string_unchecked("quotedName", 10, 10);
x_226 = l_Lean_Name_mkStr4(x_222, x_223, x_224, x_225);
x_227 = lean_mk_string_unchecked("`", 1, 1);
x_228 = lean_mk_string_unchecked(".", 1, 1);
x_229 = l_String_intercalate(x_228, x_221);
lean_dec(x_228);
x_230 = lean_string_append(x_227, x_229);
lean_dec(x_229);
x_231 = lean_box(2);
x_232 = l_Lean_Syntax_mkNameLit(x_230, x_231);
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_mk_empty_array_with_capacity(x_233);
x_235 = lean_array_push(x_234, x_232);
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_226);
lean_ctor_set(x_236, 2, x_235);
x_115 = x_236;
goto block_217;
}
block_217:
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_st_ref_get(x_9, x_98);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
x_120 = lean_ctor_get(x_8, 5);
lean_inc(x_120);
x_121 = lean_box(0);
x_122 = lean_unbox(x_121);
x_123 = l_Lean_SourceInfo_fromRef(x_120, x_122);
x_124 = lean_ctor_get(x_8, 10);
lean_inc(x_124);
lean_dec(x_8);
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
lean_dec(x_118);
x_126 = l_Lean_Environment_mainModule(x_125);
lean_dec(x_125);
x_127 = lean_mk_string_unchecked("Lean", 4, 4);
x_128 = lean_mk_string_unchecked("Parser", 6, 6);
x_129 = lean_mk_string_unchecked("Term", 4, 4);
x_130 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
x_131 = l_Lean_Name_mkStr4(x_127, x_128, x_129, x_130);
x_132 = lean_mk_string_unchecked("withAntiquot", 12, 12);
lean_inc(x_132);
x_133 = l_String_toSubstring_x27(x_132);
lean_inc(x_132);
x_134 = l_Lean_Name_mkStr1(x_132);
lean_inc(x_124);
lean_inc(x_126);
x_135 = l_Lean_addMacroScope(x_126, x_134, x_124);
lean_inc(x_128);
lean_inc(x_127);
x_136 = l_Lean_Name_mkStr3(x_127, x_128, x_132);
x_137 = lean_box(0);
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 1, x_137);
lean_ctor_set(x_116, 0, x_136);
x_138 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_99;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_116);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_123);
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_133);
lean_ctor_set(x_140, 2, x_135);
lean_ctor_set(x_140, 3, x_139);
x_141 = lean_mk_string_unchecked("null", 4, 4);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_128);
lean_inc(x_127);
x_144 = l_Lean_Name_mkStr4(x_127, x_128, x_129, x_143);
x_145 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_123);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_123);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("mkAntiquot", 10, 10);
lean_inc(x_147);
x_148 = l_String_toSubstring_x27(x_147);
lean_inc(x_147);
x_149 = l_Lean_Name_mkStr1(x_147);
lean_inc(x_124);
lean_inc(x_126);
x_150 = l_Lean_addMacroScope(x_126, x_149, x_124);
lean_inc(x_128);
lean_inc(x_127);
x_151 = l_Lean_Name_mkStr3(x_127, x_128, x_147);
lean_inc(x_151);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_137);
if (lean_is_scalar(x_101)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_101;
 lean_ctor_set_tag(x_153, 0);
}
lean_ctor_set(x_153, 0, x_151);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_138);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
lean_inc(x_123);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_123);
lean_ctor_set(x_156, 1, x_148);
lean_ctor_set(x_156, 2, x_150);
lean_ctor_set(x_156, 3, x_155);
x_157 = lean_box(2);
x_158 = l_Lean_Syntax_mkStrLit(x_114, x_157);
lean_dec(x_114);
if (x_3 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_mk_string_unchecked("Bool", 4, 4);
x_160 = lean_mk_string_unchecked("false", 5, 5);
x_161 = l_Lean_Name_mkStr2(x_159, x_160);
x_162 = l_Lean_mkCIdent(x_161);
x_11 = x_131;
x_12 = x_146;
x_13 = x_142;
x_14 = x_115;
x_15 = x_119;
x_16 = x_127;
x_17 = x_128;
x_18 = x_120;
x_19 = x_156;
x_20 = x_158;
x_21 = x_126;
x_22 = x_144;
x_23 = x_137;
x_24 = x_138;
x_25 = x_124;
x_26 = x_140;
x_27 = x_123;
x_28 = x_162;
goto block_91;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_mk_string_unchecked("Bool", 4, 4);
x_164 = lean_mk_string_unchecked("true", 4, 4);
x_165 = l_Lean_Name_mkStr2(x_163, x_164);
x_166 = l_Lean_mkCIdent(x_165);
x_11 = x_131;
x_12 = x_146;
x_13 = x_142;
x_14 = x_115;
x_15 = x_119;
x_16 = x_127;
x_17 = x_128;
x_18 = x_120;
x_19 = x_156;
x_20 = x_158;
x_21 = x_126;
x_22 = x_144;
x_23 = x_137;
x_24 = x_138;
x_25 = x_124;
x_26 = x_140;
x_27 = x_123;
x_28 = x_166;
goto block_91;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_167 = lean_ctor_get(x_116, 0);
x_168 = lean_ctor_get(x_116, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_116);
x_169 = lean_ctor_get(x_8, 5);
lean_inc(x_169);
x_170 = lean_box(0);
x_171 = lean_unbox(x_170);
x_172 = l_Lean_SourceInfo_fromRef(x_169, x_171);
x_173 = lean_ctor_get(x_8, 10);
lean_inc(x_173);
lean_dec(x_8);
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
lean_dec(x_167);
x_175 = l_Lean_Environment_mainModule(x_174);
lean_dec(x_174);
x_176 = lean_mk_string_unchecked("Lean", 4, 4);
x_177 = lean_mk_string_unchecked("Parser", 6, 6);
x_178 = lean_mk_string_unchecked("Term", 4, 4);
x_179 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
x_180 = l_Lean_Name_mkStr4(x_176, x_177, x_178, x_179);
x_181 = lean_mk_string_unchecked("withAntiquot", 12, 12);
lean_inc(x_181);
x_182 = l_String_toSubstring_x27(x_181);
lean_inc(x_181);
x_183 = l_Lean_Name_mkStr1(x_181);
lean_inc(x_173);
lean_inc(x_175);
x_184 = l_Lean_addMacroScope(x_175, x_183, x_173);
lean_inc(x_177);
lean_inc(x_176);
x_185 = l_Lean_Name_mkStr3(x_176, x_177, x_181);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_99;
 lean_ctor_set_tag(x_189, 1);
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_172);
x_190 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_190, 0, x_172);
lean_ctor_set(x_190, 1, x_182);
lean_ctor_set(x_190, 2, x_184);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_mk_string_unchecked("null", 4, 4);
x_192 = l_Lean_Name_mkStr1(x_191);
x_193 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_177);
lean_inc(x_176);
x_194 = l_Lean_Name_mkStr4(x_176, x_177, x_178, x_193);
x_195 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_172);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_172);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_mk_string_unchecked("mkAntiquot", 10, 10);
lean_inc(x_197);
x_198 = l_String_toSubstring_x27(x_197);
lean_inc(x_197);
x_199 = l_Lean_Name_mkStr1(x_197);
lean_inc(x_173);
lean_inc(x_175);
x_200 = l_Lean_addMacroScope(x_175, x_199, x_173);
lean_inc(x_177);
lean_inc(x_176);
x_201 = l_Lean_Name_mkStr3(x_176, x_177, x_197);
lean_inc(x_201);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_186);
if (lean_is_scalar(x_101)) {
 x_203 = lean_alloc_ctor(0, 1, 0);
} else {
 x_203 = x_101;
 lean_ctor_set_tag(x_203, 0);
}
lean_ctor_set(x_203, 0, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_188);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_172);
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_172);
lean_ctor_set(x_206, 1, x_198);
lean_ctor_set(x_206, 2, x_200);
lean_ctor_set(x_206, 3, x_205);
x_207 = lean_box(2);
x_208 = l_Lean_Syntax_mkStrLit(x_114, x_207);
lean_dec(x_114);
if (x_3 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_mk_string_unchecked("Bool", 4, 4);
x_210 = lean_mk_string_unchecked("false", 5, 5);
x_211 = l_Lean_Name_mkStr2(x_209, x_210);
x_212 = l_Lean_mkCIdent(x_211);
x_11 = x_180;
x_12 = x_196;
x_13 = x_192;
x_14 = x_115;
x_15 = x_168;
x_16 = x_176;
x_17 = x_177;
x_18 = x_169;
x_19 = x_206;
x_20 = x_208;
x_21 = x_175;
x_22 = x_194;
x_23 = x_186;
x_24 = x_188;
x_25 = x_173;
x_26 = x_190;
x_27 = x_172;
x_28 = x_212;
goto block_91;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_mk_string_unchecked("Bool", 4, 4);
x_214 = lean_mk_string_unchecked("true", 4, 4);
x_215 = l_Lean_Name_mkStr2(x_213, x_214);
x_216 = l_Lean_mkCIdent(x_215);
x_11 = x_180;
x_12 = x_196;
x_13 = x_192;
x_14 = x_115;
x_15 = x_168;
x_16 = x_176;
x_17 = x_177;
x_18 = x_169;
x_19 = x_206;
x_20 = x_208;
x_21 = x_175;
x_22 = x_194;
x_23 = x_186;
x_24 = x_188;
x_25 = x_173;
x_26 = x_190;
x_27 = x_172;
x_28 = x_216;
goto block_91;
}
}
}
}
default: 
{
uint8_t x_237; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_2);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_102);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_102, 0);
lean_dec(x_238);
x_239 = lean_ctor_get(x_103, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_103, 1);
lean_inc(x_240);
lean_dec(x_103);
x_241 = l_Lean_Name_num___override(x_239, x_240);
lean_ctor_set(x_102, 0, x_241);
x_242 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_8);
lean_dec(x_102);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_102, 1);
x_244 = lean_ctor_get(x_102, 2);
x_245 = lean_ctor_get(x_102, 3);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_102);
x_246 = lean_ctor_get(x_103, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_103, 1);
lean_inc(x_247);
lean_dec(x_103);
x_248 = l_Lean_Name_num___override(x_246, x_247);
x_249 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_243);
lean_ctor_set(x_249, 2, x_244);
lean_ctor_set(x_249, 3, x_245);
x_250 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(x_249, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_8);
lean_dec(x_249);
return x_250;
}
}
}
}
block_91:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_27);
x_29 = l_Lean_Syntax_node3(x_27, x_13, x_20, x_14, x_28);
lean_inc(x_11);
lean_inc(x_27);
x_30 = l_Lean_Syntax_node2(x_27, x_11, x_19, x_29);
x_31 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_27);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_32);
lean_inc(x_12);
lean_inc(x_22);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node3(x_27, x_22, x_12, x_30, x_32);
x_34 = lean_mk_string_unchecked("leadingNode", 11, 11);
lean_inc(x_34);
x_35 = l_String_toSubstring_x27(x_34);
lean_inc(x_34);
x_36 = l_Lean_Name_mkStr1(x_34);
lean_inc(x_25);
x_37 = l_Lean_addMacroScope(x_21, x_36, x_25);
lean_inc(x_17);
lean_inc(x_16);
x_38 = l_Lean_Name_mkStr3(x_16, x_17, x_34);
lean_inc(x_23);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_38);
lean_inc(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_27);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_42);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_27);
x_44 = l_Lean_Syntax_node3(x_27, x_13, x_14, x_1, x_2);
lean_inc(x_11);
lean_inc(x_27);
x_45 = l_Lean_Syntax_node2(x_27, x_11, x_43, x_44);
lean_inc(x_27);
x_46 = l_Lean_Syntax_node3(x_27, x_22, x_12, x_45, x_32);
lean_inc(x_13);
lean_inc(x_27);
x_47 = l_Lean_Syntax_node2(x_27, x_13, x_33, x_46);
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_ctor_get(x_48, 1);
x_50 = l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_st_ref_get(x_9, x_15);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_11);
x_54 = l_Lean_Syntax_node2(x_27, x_11, x_26, x_47);
x_55 = l_Lean_SourceInfo_fromRef(x_18, x_50);
lean_dec(x_18);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Environment_mainModule(x_56);
lean_dec(x_56);
x_58 = lean_mk_string_unchecked("withCache", 9, 9);
lean_inc(x_58);
x_59 = l_String_toSubstring_x27(x_58);
lean_inc(x_58);
x_60 = l_Lean_Name_mkStr1(x_58);
x_61 = l_Lean_addMacroScope(x_57, x_60, x_25);
x_62 = l_Lean_Name_mkStr3(x_16, x_17, x_58);
lean_inc(x_62);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_24);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_55);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_66);
lean_inc(x_55);
x_68 = l_Lean_Syntax_node2(x_55, x_13, x_14, x_54);
x_69 = l_Lean_Syntax_node2(x_55, x_11, x_67, x_68);
lean_ctor_set(x_51, 0, x_69);
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_70 = lean_ctor_get(x_51, 0);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_51);
lean_inc(x_11);
x_72 = l_Lean_Syntax_node2(x_27, x_11, x_26, x_47);
x_73 = l_Lean_SourceInfo_fromRef(x_18, x_50);
lean_dec(x_18);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lean_Environment_mainModule(x_74);
lean_dec(x_74);
x_76 = lean_mk_string_unchecked("withCache", 9, 9);
lean_inc(x_76);
x_77 = l_String_toSubstring_x27(x_76);
lean_inc(x_76);
x_78 = l_Lean_Name_mkStr1(x_76);
x_79 = l_Lean_addMacroScope(x_75, x_78, x_25);
x_80 = l_Lean_Name_mkStr3(x_16, x_17, x_76);
lean_inc(x_80);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_23);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_24);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_73);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_84);
lean_inc(x_73);
x_86 = l_Lean_Syntax_node2(x_73, x_13, x_14, x_72);
x_87 = l_Lean_Syntax_node2(x_73, x_11, x_85, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_71);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
x_89 = l_Lean_Syntax_node2(x_27, x_11, x_26, x_47);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_15);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0_spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0_spec__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyM___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_spec__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("leading_parser", 14, 14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_75; uint8_t x_76; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_1, x_51);
x_76 = l_Lean_Syntax_isNone(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(2u);
lean_inc(x_75);
x_78 = l_Lean_Syntax_matchesNull(x_75, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Syntax_getArg(x_75, x_51);
lean_dec(x_75);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_52 = x_81;
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
goto block_74;
}
}
else
{
lean_object* x_82; 
lean_dec(x_75);
x_82 = lean_box(0);
x_52 = x_82;
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
goto block_74;
}
block_74:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(2u);
x_61 = l_Lean_Syntax_getArg(x_1, x_60);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_inc(x_61);
x_63 = l_Lean_Syntax_matchesNull(x_61, x_51);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_64 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_59);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = l_Lean_Syntax_getArg(x_61, x_50);
lean_dec(x_61);
x_66 = lean_mk_string_unchecked("withAnonymousAntiquot", 21, 21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_67 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_66);
lean_inc(x_65);
x_68 = l_Lean_Syntax_isOfKind(x_65, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_69 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_59);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Syntax_getArg(x_65, x_70);
lean_dec(x_65);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_32 = x_52;
x_33 = x_72;
x_34 = x_53;
x_35 = x_54;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
goto block_48;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_61);
x_73 = lean_box(0);
x_32 = x_52;
x_33 = x_73;
x_34 = x_53;
x_35 = x_54;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
goto block_48;
}
}
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_25 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_24, x_16, x_14, x_18, x_19, x_23, x_20, x_17, x_15, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_mk_string_unchecked("trueVal", 7, 7);
x_28 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_27);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_24, x_16, x_29, x_18, x_19, x_23, x_20, x_17, x_15, x_22);
return x_30;
}
}
block_48:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(3u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_45 = lean_box(2);
x_46 = l_Lean_Syntax_mkNumLit(x_44, x_45);
x_15 = x_39;
x_16 = x_42;
x_17 = x_38;
x_18 = x_34;
x_19 = x_35;
x_20 = x_37;
x_21 = x_33;
x_22 = x_40;
x_23 = x_36;
x_24 = x_46;
goto block_31;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_15 = x_39;
x_16 = x_42;
x_17 = x_38;
x_18 = x_34;
x_19 = x_35;
x_20 = x_37;
x_21 = x_33;
x_22 = x_40;
x_23 = x_36;
x_24 = x_47;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLeadingParserMacro___lam__0___boxed), 8, 0);
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabLeadingParserMacro___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("leading_parser", 14, 14);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLeadingParserMacro", 22, 22);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLeadingParserMacro), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLeadingParserMacro", 22, 22);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(162u);
x_8 = lean_unsigned_to_nat(38u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(166u);
x_11 = lean_unsigned_to_nat(33u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(42u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(64u);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_mk_string_unchecked("invalid `trailing_parser` macro, it must be used in definitions", 63, 63);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_76, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_8);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_4);
x_78 = lean_ctor_get(x_12, 0);
lean_inc(x_78);
lean_dec(x_12);
x_79 = lean_box(0);
lean_inc(x_78);
x_80 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_79, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = l_Lean_quoteNameMk(x_78);
x_15 = x_81;
goto block_74;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_78);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_mk_string_unchecked("Lean", 4, 4);
x_84 = lean_mk_string_unchecked("Parser", 6, 6);
x_85 = lean_mk_string_unchecked("Term", 4, 4);
x_86 = lean_mk_string_unchecked("quotedName", 10, 10);
x_87 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_86);
x_88 = lean_mk_string_unchecked("`", 1, 1);
x_89 = lean_mk_string_unchecked(".", 1, 1);
x_90 = l_String_intercalate(x_89, x_82);
lean_dec(x_89);
x_91 = lean_string_append(x_88, x_90);
lean_dec(x_90);
x_92 = lean_box(2);
x_93 = l_Lean_Syntax_mkNameLit(x_91, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_mk_empty_array_with_capacity(x_94);
x_96 = lean_array_push(x_95, x_93);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_87);
lean_ctor_set(x_97, 2, x_96);
x_15 = x_97;
goto block_74;
}
}
block_74:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_get(x_9, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_8, 5);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_SourceInfo_fromRef(x_19, x_21);
lean_dec(x_19);
x_23 = lean_ctor_get(x_8, 10);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Environment_mainModule(x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Parser", 6, 6);
x_28 = lean_mk_string_unchecked("Term", 4, 4);
x_29 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_27);
lean_inc(x_26);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
x_31 = lean_mk_string_unchecked("Lean.Parser.trailingNode", 24, 24);
x_32 = l_String_toSubstring_x27(x_31);
x_33 = lean_mk_string_unchecked("trailingNode", 12, 12);
x_34 = l_Lean_Name_mkStr3(x_26, x_27, x_33);
lean_inc(x_34);
x_35 = l_Lean_addMacroScope(x_25, x_34, x_23);
x_36 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_14;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_22);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_mk_string_unchecked("null", 4, 4);
x_42 = l_Lean_Name_mkStr1(x_41);
lean_inc(x_22);
x_43 = l_Lean_Syntax_node4(x_22, x_42, x_15, x_1, x_2, x_3);
x_44 = l_Lean_Syntax_node2(x_22, x_30, x_40, x_43);
lean_ctor_set(x_16, 0, x_44);
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_ctor_get(x_8, 5);
lean_inc(x_47);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_SourceInfo_fromRef(x_47, x_49);
lean_dec(x_47);
x_51 = lean_ctor_get(x_8, 10);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = l_Lean_Environment_mainModule(x_52);
lean_dec(x_52);
x_54 = lean_mk_string_unchecked("Lean", 4, 4);
x_55 = lean_mk_string_unchecked("Parser", 6, 6);
x_56 = lean_mk_string_unchecked("Term", 4, 4);
x_57 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_55);
lean_inc(x_54);
x_58 = l_Lean_Name_mkStr4(x_54, x_55, x_56, x_57);
x_59 = lean_mk_string_unchecked("Lean.Parser.trailingNode", 24, 24);
x_60 = l_String_toSubstring_x27(x_59);
x_61 = lean_mk_string_unchecked("trailingNode", 12, 12);
x_62 = l_Lean_Name_mkStr3(x_54, x_55, x_61);
lean_inc(x_62);
x_63 = l_Lean_addMacroScope(x_53, x_62, x_51);
x_64 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_14;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_50);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_mk_string_unchecked("null", 4, 4);
x_70 = l_Lean_Name_mkStr1(x_69);
lean_inc(x_50);
x_71 = l_Lean_Syntax_node4(x_50, x_70, x_15, x_1, x_2, x_3);
x_72 = l_Lean_Syntax_node2(x_50, x_58, x_68, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_46);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("trailing_parser", 15, 15);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_69; uint8_t x_70; 
x_16 = lean_unsigned_to_nat(0u);
x_51 = lean_unsigned_to_nat(1u);
x_69 = l_Lean_Syntax_getArg(x_1, x_51);
x_70 = l_Lean_Syntax_isNone(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_unsigned_to_nat(2u);
lean_inc(x_69);
x_72 = l_Lean_Syntax_matchesNull(x_69, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Syntax_getArg(x_69, x_51);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_52 = x_75;
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
goto block_68;
}
}
else
{
lean_object* x_76; 
lean_dec(x_69);
x_76 = lean_box(0);
x_52 = x_76;
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
goto block_68;
}
block_33:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_28 = lean_box(2);
x_29 = l_Lean_Syntax_mkNumLit(x_27, x_28);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_26, x_29, x_24, x_19, x_23, x_22, x_21, x_17, x_25, x_20);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_26, x_31, x_24, x_19, x_23, x_22, x_21, x_17, x_25, x_20);
return x_32;
}
}
block_50:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(3u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
lean_dec(x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_unsigned_to_nat(1024u);
x_46 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_47 = lean_box(2);
x_48 = l_Lean_Syntax_mkNumLit(x_46, x_47);
x_17 = x_40;
x_18 = x_35;
x_19 = x_36;
x_20 = x_42;
x_21 = x_39;
x_22 = x_38;
x_23 = x_37;
x_24 = x_44;
x_25 = x_41;
x_26 = x_48;
goto block_33;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_34, 0);
lean_inc(x_49);
lean_dec(x_34);
x_17 = x_40;
x_18 = x_35;
x_19 = x_36;
x_20 = x_42;
x_21 = x_39;
x_22 = x_38;
x_23 = x_37;
x_24 = x_44;
x_25 = x_41;
x_26 = x_49;
goto block_33;
}
}
block_68:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(2u);
x_61 = l_Lean_Syntax_getArg(x_1, x_60);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_inc(x_61);
x_63 = l_Lean_Syntax_matchesNull(x_61, x_60);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_64 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_59);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_Syntax_getArg(x_61, x_51);
lean_dec(x_61);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_34 = x_52;
x_35 = x_66;
x_36 = x_53;
x_37 = x_54;
x_38 = x_55;
x_39 = x_56;
x_40 = x_57;
x_41 = x_58;
x_42 = x_59;
goto block_50;
}
}
else
{
lean_object* x_67; 
lean_dec(x_61);
x_67 = lean_box(0);
x_34 = x_52;
x_35 = x_67;
x_36 = x_53;
x_37 = x_54;
x_38 = x_55;
x_39 = x_56;
x_40 = x_57;
x_41 = x_58;
x_42 = x_59;
goto block_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTrailingParserMacro___lam__0___boxed), 8, 0);
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabTrailingParserMacro___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("trailing_parser", 15, 15);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabTrailingParserMacro", 23, 23);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTrailingParserMacro), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabTrailingParserMacro", 23, 23);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(174u);
x_8 = lean_unsigned_to_nat(39u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(178u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(66u);
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
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Syntax_getPos_x3f(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg(x_5, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_FileMap_toPosition(x_11, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_FileMap_toPosition(x_15, x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_elabPanic___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPanic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("panic", 5, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_29; 
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
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_7);
x_30 = l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_8, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_3, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_st_ref_get(x_8, x_39);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_48 = lean_ctor_get(x_7, 5);
lean_inc(x_48);
x_49 = lean_box(0);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_SourceInfo_fromRef(x_48, x_50);
lean_dec(x_48);
x_52 = lean_ctor_get(x_7, 10);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lean_Environment_mainModule(x_53);
lean_dec(x_53);
x_55 = lean_mk_string_unchecked("app", 3, 3);
x_56 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_55);
x_57 = lean_mk_string_unchecked("panicWithPos", 12, 12);
lean_inc(x_57);
x_58 = l_String_toSubstring_x27(x_57);
x_59 = l_Lean_Name_mkStr1(x_57);
lean_inc(x_59);
x_60 = l_Lean_addMacroScope(x_54, x_59, x_52);
x_61 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_61);
lean_ctor_set(x_43, 0, x_59);
x_62 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_43);
lean_inc(x_51);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_36);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = l_Lean_Environment_mainModule(x_42);
lean_dec(x_42);
x_67 = l_Lean_Name_toString(x_66, x_15, x_47);
x_68 = lean_box(2);
x_69 = l_Lean_Syntax_mkStrLit(x_67, x_68);
lean_dec(x_67);
x_70 = lean_ctor_get(x_31, 0);
lean_inc(x_70);
x_71 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_72 = l_Lean_Syntax_mkNumLit(x_71, x_68);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_dec(x_31);
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_73);
x_75 = l_Lean_Syntax_mkNumLit(x_74, x_68);
lean_inc(x_51);
x_76 = l_Lean_Syntax_node4(x_51, x_65, x_69, x_72, x_75, x_41);
x_77 = l_Lean_Syntax_node2(x_51, x_56, x_63, x_76);
x_16 = x_77;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_46;
goto block_28;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_78 = lean_ctor_get(x_43, 0);
x_79 = lean_ctor_get(x_43, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_43);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_81 = lean_ctor_get(x_7, 5);
lean_inc(x_81);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_SourceInfo_fromRef(x_81, x_83);
lean_dec(x_81);
x_85 = lean_ctor_get(x_7, 10);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
lean_dec(x_78);
x_87 = l_Lean_Environment_mainModule(x_86);
lean_dec(x_86);
x_88 = lean_mk_string_unchecked("app", 3, 3);
x_89 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_88);
x_90 = lean_mk_string_unchecked("panicWithPos", 12, 12);
lean_inc(x_90);
x_91 = l_String_toSubstring_x27(x_90);
x_92 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_92);
x_93 = l_Lean_addMacroScope(x_87, x_92, x_85);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_96);
lean_ctor_set(x_36, 0, x_95);
lean_inc(x_84);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_84);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_36);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Environment_mainModule(x_42);
lean_dec(x_42);
x_101 = l_Lean_Name_toString(x_100, x_15, x_80);
x_102 = lean_box(2);
x_103 = l_Lean_Syntax_mkStrLit(x_101, x_102);
lean_dec(x_101);
x_104 = lean_ctor_get(x_31, 0);
lean_inc(x_104);
x_105 = l___private_Init_Data_Repr_0__Nat_reprFast(x_104);
x_106 = l_Lean_Syntax_mkNumLit(x_105, x_102);
x_107 = lean_ctor_get(x_31, 1);
lean_inc(x_107);
lean_dec(x_31);
x_108 = l___private_Init_Data_Repr_0__Nat_reprFast(x_107);
x_109 = l_Lean_Syntax_mkNumLit(x_108, x_102);
lean_inc(x_84);
x_110 = l_Lean_Syntax_node4(x_84, x_99, x_103, x_106, x_109, x_41);
x_111 = l_Lean_Syntax_node2(x_84, x_89, x_97, x_110);
x_16 = x_111;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_79;
goto block_28;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_34, 0);
lean_inc(x_112);
lean_dec(x_34);
x_113 = lean_ctor_get(x_38, 0);
lean_inc(x_113);
lean_dec(x_38);
x_114 = lean_st_ref_get(x_8, x_39);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_119 = lean_ctor_get(x_7, 5);
lean_inc(x_119);
x_120 = lean_box(0);
x_121 = lean_unbox(x_120);
x_122 = l_Lean_SourceInfo_fromRef(x_119, x_121);
lean_dec(x_119);
x_123 = lean_ctor_get(x_7, 10);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
lean_dec(x_116);
x_125 = l_Lean_Environment_mainModule(x_124);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked("app", 3, 3);
x_127 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_126);
x_128 = lean_mk_string_unchecked("panicWithPosWithDecl", 20, 20);
lean_inc(x_128);
x_129 = l_String_toSubstring_x27(x_128);
x_130 = l_Lean_Name_mkStr1(x_128);
lean_inc(x_130);
x_131 = l_Lean_addMacroScope(x_125, x_130, x_123);
x_132 = lean_box(0);
lean_ctor_set_tag(x_114, 1);
lean_ctor_set(x_114, 1, x_132);
lean_ctor_set(x_114, 0, x_130);
x_133 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_133);
lean_ctor_set(x_36, 0, x_114);
lean_inc(x_122);
x_134 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_129);
lean_ctor_set(x_134, 2, x_131);
lean_ctor_set(x_134, 3, x_36);
x_135 = lean_mk_string_unchecked("null", 4, 4);
x_136 = l_Lean_Name_mkStr1(x_135);
x_137 = l_Lean_Environment_mainModule(x_112);
lean_dec(x_112);
lean_inc(x_118);
x_138 = l_Lean_Name_toString(x_137, x_15, x_118);
x_139 = lean_box(2);
x_140 = l_Lean_Syntax_mkStrLit(x_138, x_139);
lean_dec(x_138);
x_141 = l_Lean_Name_toString(x_113, x_15, x_118);
x_142 = l_Lean_Syntax_mkStrLit(x_141, x_139);
lean_dec(x_141);
x_143 = lean_ctor_get(x_31, 0);
lean_inc(x_143);
x_144 = l___private_Init_Data_Repr_0__Nat_reprFast(x_143);
x_145 = l_Lean_Syntax_mkNumLit(x_144, x_139);
x_146 = lean_ctor_get(x_31, 1);
lean_inc(x_146);
lean_dec(x_31);
x_147 = l___private_Init_Data_Repr_0__Nat_reprFast(x_146);
x_148 = l_Lean_Syntax_mkNumLit(x_147, x_139);
lean_inc(x_122);
x_149 = l_Lean_Syntax_node5(x_122, x_136, x_140, x_142, x_145, x_148, x_41);
x_150 = l_Lean_Syntax_node2(x_122, x_127, x_134, x_149);
x_16 = x_150;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_117;
goto block_28;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_151 = lean_ctor_get(x_114, 0);
x_152 = lean_ctor_get(x_114, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_114);
x_153 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_154 = lean_ctor_get(x_7, 5);
lean_inc(x_154);
x_155 = lean_box(0);
x_156 = lean_unbox(x_155);
x_157 = l_Lean_SourceInfo_fromRef(x_154, x_156);
lean_dec(x_154);
x_158 = lean_ctor_get(x_7, 10);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
lean_dec(x_151);
x_160 = l_Lean_Environment_mainModule(x_159);
lean_dec(x_159);
x_161 = lean_mk_string_unchecked("app", 3, 3);
x_162 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_161);
x_163 = lean_mk_string_unchecked("panicWithPosWithDecl", 20, 20);
lean_inc(x_163);
x_164 = l_String_toSubstring_x27(x_163);
x_165 = l_Lean_Name_mkStr1(x_163);
lean_inc(x_165);
x_166 = l_Lean_addMacroScope(x_160, x_165, x_158);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_169);
lean_ctor_set(x_36, 0, x_168);
lean_inc(x_157);
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_157);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_166);
lean_ctor_set(x_170, 3, x_36);
x_171 = lean_mk_string_unchecked("null", 4, 4);
x_172 = l_Lean_Name_mkStr1(x_171);
x_173 = l_Lean_Environment_mainModule(x_112);
lean_dec(x_112);
lean_inc(x_153);
x_174 = l_Lean_Name_toString(x_173, x_15, x_153);
x_175 = lean_box(2);
x_176 = l_Lean_Syntax_mkStrLit(x_174, x_175);
lean_dec(x_174);
x_177 = l_Lean_Name_toString(x_113, x_15, x_153);
x_178 = l_Lean_Syntax_mkStrLit(x_177, x_175);
lean_dec(x_177);
x_179 = lean_ctor_get(x_31, 0);
lean_inc(x_179);
x_180 = l___private_Init_Data_Repr_0__Nat_reprFast(x_179);
x_181 = l_Lean_Syntax_mkNumLit(x_180, x_175);
x_182 = lean_ctor_get(x_31, 1);
lean_inc(x_182);
lean_dec(x_31);
x_183 = l___private_Init_Data_Repr_0__Nat_reprFast(x_182);
x_184 = l_Lean_Syntax_mkNumLit(x_183, x_175);
lean_inc(x_157);
x_185 = l_Lean_Syntax_node5(x_157, x_172, x_176, x_178, x_181, x_184, x_41);
x_186 = l_Lean_Syntax_node2(x_157, x_162, x_170, x_185);
x_16 = x_186;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_152;
goto block_28;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_36, 0);
x_188 = lean_ctor_get(x_36, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_36);
x_189 = lean_unsigned_to_nat(1u);
x_190 = l_Lean_Syntax_getArg(x_1, x_189);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_191 = lean_ctor_get(x_34, 0);
lean_inc(x_191);
lean_dec(x_34);
x_192 = lean_st_ref_get(x_8, x_188);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
x_196 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_197 = lean_ctor_get(x_7, 5);
lean_inc(x_197);
x_198 = lean_box(0);
x_199 = lean_unbox(x_198);
x_200 = l_Lean_SourceInfo_fromRef(x_197, x_199);
lean_dec(x_197);
x_201 = lean_ctor_get(x_7, 10);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 0);
lean_inc(x_202);
lean_dec(x_193);
x_203 = l_Lean_Environment_mainModule(x_202);
lean_dec(x_202);
x_204 = lean_mk_string_unchecked("app", 3, 3);
x_205 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_204);
x_206 = lean_mk_string_unchecked("panicWithPos", 12, 12);
lean_inc(x_206);
x_207 = l_String_toSubstring_x27(x_206);
x_208 = l_Lean_Name_mkStr1(x_206);
lean_inc(x_208);
x_209 = l_Lean_addMacroScope(x_203, x_208, x_201);
x_210 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_195;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
lean_inc(x_200);
x_214 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_214, 0, x_200);
lean_ctor_set(x_214, 1, x_207);
lean_ctor_set(x_214, 2, x_209);
lean_ctor_set(x_214, 3, x_213);
x_215 = lean_mk_string_unchecked("null", 4, 4);
x_216 = l_Lean_Name_mkStr1(x_215);
x_217 = l_Lean_Environment_mainModule(x_191);
lean_dec(x_191);
x_218 = l_Lean_Name_toString(x_217, x_15, x_196);
x_219 = lean_box(2);
x_220 = l_Lean_Syntax_mkStrLit(x_218, x_219);
lean_dec(x_218);
x_221 = lean_ctor_get(x_31, 0);
lean_inc(x_221);
x_222 = l___private_Init_Data_Repr_0__Nat_reprFast(x_221);
x_223 = l_Lean_Syntax_mkNumLit(x_222, x_219);
x_224 = lean_ctor_get(x_31, 1);
lean_inc(x_224);
lean_dec(x_31);
x_225 = l___private_Init_Data_Repr_0__Nat_reprFast(x_224);
x_226 = l_Lean_Syntax_mkNumLit(x_225, x_219);
lean_inc(x_200);
x_227 = l_Lean_Syntax_node4(x_200, x_216, x_220, x_223, x_226, x_190);
x_228 = l_Lean_Syntax_node2(x_200, x_205, x_214, x_227);
x_16 = x_228;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_194;
goto block_28;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_229 = lean_ctor_get(x_34, 0);
lean_inc(x_229);
lean_dec(x_34);
x_230 = lean_ctor_get(x_187, 0);
lean_inc(x_230);
lean_dec(x_187);
x_231 = lean_st_ref_get(x_8, x_188);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic___lam__0___boxed), 1, 0);
x_236 = lean_ctor_get(x_7, 5);
lean_inc(x_236);
x_237 = lean_box(0);
x_238 = lean_unbox(x_237);
x_239 = l_Lean_SourceInfo_fromRef(x_236, x_238);
lean_dec(x_236);
x_240 = lean_ctor_get(x_7, 10);
lean_inc(x_240);
x_241 = lean_ctor_get(x_232, 0);
lean_inc(x_241);
lean_dec(x_232);
x_242 = l_Lean_Environment_mainModule(x_241);
lean_dec(x_241);
x_243 = lean_mk_string_unchecked("app", 3, 3);
x_244 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_243);
x_245 = lean_mk_string_unchecked("panicWithPosWithDecl", 20, 20);
lean_inc(x_245);
x_246 = l_String_toSubstring_x27(x_245);
x_247 = l_Lean_Name_mkStr1(x_245);
lean_inc(x_247);
x_248 = l_Lean_addMacroScope(x_242, x_247, x_240);
x_249 = lean_box(0);
if (lean_is_scalar(x_234)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_234;
 lean_ctor_set_tag(x_250, 1);
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_239);
x_253 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_253, 0, x_239);
lean_ctor_set(x_253, 1, x_246);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_252);
x_254 = lean_mk_string_unchecked("null", 4, 4);
x_255 = l_Lean_Name_mkStr1(x_254);
x_256 = l_Lean_Environment_mainModule(x_229);
lean_dec(x_229);
lean_inc(x_235);
x_257 = l_Lean_Name_toString(x_256, x_15, x_235);
x_258 = lean_box(2);
x_259 = l_Lean_Syntax_mkStrLit(x_257, x_258);
lean_dec(x_257);
x_260 = l_Lean_Name_toString(x_230, x_15, x_235);
x_261 = l_Lean_Syntax_mkStrLit(x_260, x_258);
lean_dec(x_260);
x_262 = lean_ctor_get(x_31, 0);
lean_inc(x_262);
x_263 = l___private_Init_Data_Repr_0__Nat_reprFast(x_262);
x_264 = l_Lean_Syntax_mkNumLit(x_263, x_258);
x_265 = lean_ctor_get(x_31, 1);
lean_inc(x_265);
lean_dec(x_31);
x_266 = l___private_Init_Data_Repr_0__Nat_reprFast(x_265);
x_267 = l_Lean_Syntax_mkNumLit(x_266, x_258);
lean_inc(x_239);
x_268 = l_Lean_Syntax_node5(x_239, x_255, x_259, x_261, x_264, x_267, x_190);
x_269 = l_Lean_Syntax_node2(x_239, x_244, x_253, x_268);
x_16 = x_269;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_233;
goto block_28;
}
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(x_15);
x_25 = lean_box(x_15);
lean_inc(x_16);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_25);
x_27 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_16, x_26, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPanic___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabPanic___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("panic", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabPanic", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabPanic", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(180u);
x_8 = lean_unsigned_to_nat(44u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(189u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(48u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_SourceInfo_fromRef(x_3, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("panic", 5, 5);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_mk_string_unchecked("panic!", 6, 6);
lean_inc(x_6);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("str", 3, 3);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("\"unreachable code has been reached\"", 35, 35);
lean_inc(x_6);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_6);
x_18 = l_Lean_Syntax_node1(x_6, x_15, x_17);
x_19 = l_Lean_Syntax_node2(x_6, x_11, x_13, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandUnreachable___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandUnreachable___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandUnreachable(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("unreachable", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandUnreachable", 17, 17);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUnreachable___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandUnreachable", 17, 17);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(191u);
x_8 = lean_unsigned_to_nat(47u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(192u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_8);
x_13 = lean_unsigned_to_nat(51u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(68u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandAssert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("assert", 6, 6);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
lean_inc(x_12);
x_15 = l_Lean_Syntax_reprint(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
x_20 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_19);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_19);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("panic", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_28);
x_30 = lean_mk_string_unchecked("panic!", 6, 6);
lean_inc(x_19);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("paren", 5, 5);
x_33 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_32);
x_34 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("str", 3, 3);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_mk_string_unchecked("\"assertion violation\"", 21, 21);
lean_inc(x_19);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_19);
x_40 = l_Lean_Syntax_node1(x_19, x_37, x_39);
x_41 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node3(x_19, x_33, x_35, x_40, x_42);
lean_inc(x_19);
x_44 = l_Lean_Syntax_node2(x_19, x_29, x_31, x_43);
x_45 = l_Lean_Syntax_node6(x_19, x_21, x_23, x_12, x_25, x_14, x_27, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_2, 5);
x_49 = lean_box(0);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_SourceInfo_fromRef(x_48, x_50);
x_52 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_51);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_51);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_51);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked("panic", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_60);
x_62 = lean_mk_string_unchecked("panic!", 6, 6);
lean_inc(x_51);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("paren", 5, 5);
x_65 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_64);
x_66 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_51);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("term_++_", 8, 8);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = lean_mk_string_unchecked("str", 3, 3);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = lean_mk_string_unchecked("\"assertion violation: \"", 23, 23);
lean_inc(x_51);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_51);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_51);
x_74 = l_Lean_Syntax_node1(x_51, x_71, x_73);
x_75 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_51);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_51);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_box(2);
x_78 = l_Lean_Syntax_mkStrLit(x_47, x_77);
lean_dec(x_47);
lean_inc(x_51);
x_79 = l_Lean_Syntax_node3(x_51, x_69, x_74, x_76, x_78);
x_80 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_51);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_51);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_51);
x_82 = l_Lean_Syntax_node3(x_51, x_65, x_67, x_79, x_81);
lean_inc(x_51);
x_83 = l_Lean_Syntax_node2(x_51, x_61, x_63, x_82);
x_84 = l_Lean_Syntax_node6(x_51, x_53, x_55, x_12, x_57, x_14, x_59, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAssert(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("assert", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandAssert", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAssert___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandAssert", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(194u);
x_8 = lean_unsigned_to_nat(42u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(200u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(46u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(58u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_BuiltinNotation___hyg_8333_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("debugAssertions", 15, 15);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("enable `debug_assert!` statements\n\nDefaults to `false` unless the Lake `buildType` is `debug`.", 94, 94);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("debugAssert", 11, 11);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_ctor_get(x_6, 2);
x_19 = l_Lean_Elab_Term_debugAssertions;
x_20 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_st_ref_get(x_7, x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_ctor_get(x_6, 5);
x_27 = lean_box(0);
x_28 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_29 = lean_unbox(x_27);
x_30 = l_Lean_SourceInfo_fromRef(x_26, x_29);
x_31 = lean_mk_string_unchecked("assert", 6, 6);
x_32 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_31);
x_33 = lean_mk_string_unchecked("assert!", 7, 7);
lean_inc(x_30);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_30);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Syntax_node4(x_30, x_32, x_34, x_28, x_36, x_17);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_ctor_get(x_6, 5);
x_41 = lean_box(0);
x_42 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_43 = lean_unbox(x_41);
x_44 = l_Lean_SourceInfo_fromRef(x_40, x_43);
x_45 = lean_mk_string_unchecked("assert", 6, 6);
x_46 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_45);
x_47 = lean_mk_string_unchecked("assert!", 7, 7);
lean_inc(x_44);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_44);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Syntax_node4(x_44, x_46, x_48, x_42, x_50, x_17);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDebugAssert___lam__0___boxed), 8, 0);
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDebugAssert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabDebugAssert___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDebugAssert__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("debugAssert", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabDebugAssert", 15, 15);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDebugAssert), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("dbgTrace", 8, 8);
lean_inc(x_7);
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
x_13 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_14 = l_Lean_Name_mkStr1(x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = l_Lean_SourceInfo_fromRef(x_18, x_15);
lean_dec(x_18);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_22);
lean_inc(x_7);
x_24 = l_String_toSubstring_x27(x_7);
x_25 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_20);
lean_inc(x_25);
lean_inc(x_21);
x_26 = l_Lean_addMacroScope(x_21, x_25, x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_19);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_34);
x_36 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("toString", 8, 8);
lean_inc(x_38);
x_39 = l_String_toSubstring_x27(x_38);
lean_inc(x_38);
x_40 = l_Lean_Name_mkStr1(x_38);
x_41 = l_Lean_addMacroScope(x_21, x_40, x_20);
x_42 = lean_mk_string_unchecked("ToString", 8, 8);
x_43 = l_Lean_Name_mkStr2(x_42, x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_inc(x_19);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_45);
lean_inc(x_33);
lean_inc(x_19);
x_47 = l_Lean_Syntax_node1(x_19, x_33, x_12);
lean_inc(x_23);
lean_inc(x_19);
x_48 = l_Lean_Syntax_node2(x_19, x_23, x_46, x_47);
x_49 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_19);
x_51 = l_Lean_Syntax_node3(x_19, x_35, x_37, x_48, x_50);
x_52 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_52);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_52);
lean_inc(x_19);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_55);
x_57 = lean_mk_string_unchecked("hole", 4, 4);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_57);
x_59 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_19);
x_61 = l_Lean_Syntax_node1(x_19, x_58, x_60);
lean_inc(x_33);
lean_inc(x_19);
x_62 = l_Lean_Syntax_node1(x_19, x_33, x_61);
x_63 = l_Array_mkArray0(lean_box(0));
lean_inc(x_33);
lean_inc(x_19);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_33);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_19);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_19);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_19);
x_67 = l_Lean_Syntax_node4(x_19, x_56, x_62, x_64, x_66, x_17);
lean_inc(x_19);
x_68 = l_Lean_Syntax_node2(x_19, x_53, x_54, x_67);
lean_inc(x_19);
x_69 = l_Lean_Syntax_node2(x_19, x_33, x_51, x_68);
x_70 = l_Lean_Syntax_node2(x_19, x_23, x_31, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_3);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Syntax_getArg(x_1, x_72);
lean_dec(x_1);
x_74 = lean_ctor_get(x_2, 5);
lean_inc(x_74);
x_75 = lean_box(0);
x_76 = lean_unbox(x_75);
x_77 = l_Lean_SourceInfo_fromRef(x_74, x_76);
lean_dec(x_74);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
lean_dec(x_2);
x_80 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_81 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_80);
lean_inc(x_7);
x_82 = l_String_toSubstring_x27(x_7);
x_83 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_83);
x_84 = l_Lean_addMacroScope(x_79, x_83, x_78);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_77);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_mk_string_unchecked("null", 4, 4);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_93 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_92);
x_94 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_77);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_77);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("termS!_", 7, 7);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_77);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_77);
x_100 = l_Lean_Syntax_node2(x_77, x_97, x_99, x_12);
x_101 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_77);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_77);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_77);
x_103 = l_Lean_Syntax_node3(x_77, x_93, x_95, x_100, x_102);
x_104 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_104);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_105 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_104);
lean_inc(x_77);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_77);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_107);
x_109 = lean_mk_string_unchecked("hole", 4, 4);
x_110 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_109);
x_111 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_77);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_77);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_77);
x_113 = l_Lean_Syntax_node1(x_77, x_110, x_112);
lean_inc(x_91);
lean_inc(x_77);
x_114 = l_Lean_Syntax_node1(x_77, x_91, x_113);
x_115 = l_Array_mkArray0(lean_box(0));
lean_inc(x_91);
lean_inc(x_77);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_77);
lean_ctor_set(x_116, 1, x_91);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_77);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_77);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_77);
x_119 = l_Lean_Syntax_node4(x_77, x_108, x_114, x_116, x_118, x_73);
lean_inc(x_77);
x_120 = l_Lean_Syntax_node2(x_77, x_105, x_106, x_119);
lean_inc(x_77);
x_121 = l_Lean_Syntax_node2(x_77, x_91, x_103, x_120);
x_122 = l_Lean_Syntax_node2(x_77, x_81, x_89, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_3);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("dbgTrace", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandDbgTrace", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDbgTrace), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandDbgTrace", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(202u);
x_8 = lean_unsigned_to_nat(44u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(205u);
x_11 = lean_unsigned_to_nat(70u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(48u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(62u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_unbox(x_15);
lean_inc(x_2);
x_18 = l_Lean_Meta_mkFreshTypeMVar(x_17, x_16, x_2, x_3, x_4, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_7 = x_19;
x_8 = x_20;
goto block_14;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_7 = x_21;
x_8 = x_6;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Meta_mkLabeledSorry(x_7, x_11, x_12, x_2, x_3, x_4, x_5, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSorry___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSorry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabSorry", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSorry___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabSorry", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(207u);
x_8 = lean_unsigned_to_nat(29u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(209u);
x_11 = lean_unsigned_to_nat(64u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(33u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_instInhabitedTSyntax(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("app", 3, 3);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("Prod.mk", 7, 7);
x_28 = l_String_toSubstring_x27(x_27);
x_29 = lean_mk_string_unchecked("Prod", 4, 4);
x_30 = lean_mk_string_unchecked("mk", 2, 2);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
lean_inc(x_31);
x_32 = l_Lean_addMacroScope(x_21, x_31, x_20);
x_33 = lean_box(0);
lean_inc(x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_19);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_array_get(x_15, x_1, x_10);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node2(x_19, x_41, x_42, x_3);
x_44 = l_Lean_Syntax_node2(x_19, x_26, x_39, x_43);
x_2 = x_10;
x_3 = x_44;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("term", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_instInhabitedTSyntax(x_10);
lean_dec(x_10);
x_12 = l_Array_back_x21(lean_box(0), x_11, x_1);
x_13 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_6, x_12, x_2, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkPairs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_instInhabitedTSyntax(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("app", 3, 3);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("PProd.mk", 8, 8);
x_28 = l_String_toSubstring_x27(x_27);
x_29 = lean_mk_string_unchecked("PProd", 5, 5);
x_30 = lean_mk_string_unchecked("mk", 2, 2);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
lean_inc(x_31);
x_32 = l_Lean_addMacroScope(x_21, x_31, x_20);
x_33 = lean_box(0);
lean_inc(x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_19);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_array_get(x_15, x_1, x_10);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node2(x_19, x_41, x_42, x_3);
x_44 = l_Lean_Syntax_node2(x_19, x_26, x_39, x_43);
x_2 = x_10;
x_3 = x_44;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkPPairs_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("term", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_instInhabitedTSyntax(x_10);
lean_dec(x_10);
x_12 = l_Array_back_x21(lean_box(0), x_11, x_1);
x_13 = l_Lean_Elab_Term_mkPPairs_loop(x_1, x_6, x_12, x_2, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkPPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkPPairs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_instInhabitedTSyntax(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("app", 3, 3);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("MProd.mk", 8, 8);
x_28 = l_String_toSubstring_x27(x_27);
x_29 = lean_mk_string_unchecked("MProd", 5, 5);
x_30 = lean_mk_string_unchecked("mk", 2, 2);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
lean_inc(x_31);
x_32 = l_Lean_addMacroScope(x_21, x_31, x_20);
x_33 = lean_box(0);
lean_inc(x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_19);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_array_get(x_15, x_1, x_10);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node2(x_19, x_41, x_42, x_3);
x_44 = l_Lean_Syntax_node2(x_19, x_26, x_39, x_43);
x_2 = x_10;
x_3 = x_44;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkMPairs_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("term", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_instInhabitedTSyntax(x_10);
lean_dec(x_10);
x_12 = l_Array_back_x21(lean_box(0), x_11, x_1);
x_13 = l_Lean_Elab_Term_mkMPairs_loop(x_1, x_6, x_12, x_2, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkMPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkMPairs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Term_hasCDot(x_5);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_hasCDot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_23);
x_25 = lean_name_eq(x_2, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_name_eq(x_2, x_27);
lean_dec(x_27);
x_7 = x_28;
goto block_22;
}
else
{
x_7 = x_25;
goto block_22;
}
block_22:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_string_unchecked("tuple", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_8);
x_10 = lean_name_eq(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_mk_string_unchecked("cdot", 4, 4);
x_12 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_11);
x_13 = lean_name_eq(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
return x_13;
}
else
{
if (x_16 == 0)
{
lean_dec(x_15);
return x_13;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_usize_of_nat(x_14);
x_18 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_19 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0(x_3, x_17, x_18);
return x_19;
}
}
}
else
{
return x_13;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_hasCDot_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_hasCDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_hasCDot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_expandCDot_x3f_go(x_10, x_4, x_5, x_6);
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
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_20;
x_3 = x_21;
x_4 = x_15;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_4, x_3);
lean_inc(x_6);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_expandCDot_x3f_go(x_11, x_1, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_16, x_3, x_13);
x_3 = x_19;
x_4 = x_20;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_18 = lean_array_get_size(x_9);
lean_dec(x_9);
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
x_11 = x_2;
goto block_17;
}
else
{
x_11 = x_3;
goto block_17;
}
block_17:
{
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_unbox(x_10);
return x_16;
}
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_SourceInfo_fromRef(x_1, x_2);
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_box(1);
x_12 = lean_mk_string_unchecked("cdot", 4, 4);
x_13 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_mk_string_unchecked("choice", 6, 6);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_name_eq(x_15, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_array_size(x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
lean_inc(x_3);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0(x_20, x_22, x_16, x_2, x_3, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_unbox(x_11);
x_29 = l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(x_1, x_28, x_15, x_26, x_27, x_3, x_25);
lean_dec(x_3);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = l_Array_isEmpty___redArg(x_16);
if (x_34 == 0)
{
size_t x_35; lean_object* x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_array_size(x_16);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_usize_of_nat(x_36);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1(x_2, x_35, x_37, x_16, x_2, x_3, x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_55; uint8_t x_63; lean_object* x_65; uint8_t x_66; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_dec(x_43);
x_44 = l_Lean_instInhabitedSyntax;
x_45 = l_Array_instInhabited(lean_box(0));
lean_ctor_set(x_39, 1, x_45);
lean_ctor_set(x_39, 0, x_44);
x_46 = lean_array_get(x_39, x_42, x_36);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_65 = lean_array_get_size(x_42);
x_66 = lean_nat_dec_lt(x_36, x_65);
if (x_66 == 0)
{
lean_dec(x_65);
x_63 = x_34;
goto block_64;
}
else
{
if (x_66 == 0)
{
lean_dec(x_65);
x_63 = x_34;
goto block_64;
}
else
{
size_t x_67; uint8_t x_68; 
x_67 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_68 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3(x_47, x_19, x_34, x_42, x_37, x_67);
x_63 = x_68;
goto block_64;
}
}
block_54:
{
size_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_array_size(x_42);
x_51 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2(x_50, x_37, x_42);
x_52 = lean_unbox(x_11);
x_53 = l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(x_1, x_52, x_15, x_51, x_47, x_48, x_49);
lean_dec(x_48);
lean_dec(x_1);
return x_53;
}
block_62:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_15);
x_56 = lean_mk_string_unchecked("Ambiguous notation in cdot function has different numbers of '·' arguments in each alternative.", 96, 95);
x_57 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_56, x_3, x_40);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
x_48 = x_3;
x_49 = x_40;
goto block_54;
}
}
block_64:
{
if (x_63 == 0)
{
x_55 = x_19;
goto block_62;
}
else
{
x_55 = x_34;
goto block_62;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_82; uint8_t x_90; lean_object* x_92; uint8_t x_93; 
x_69 = lean_ctor_get(x_39, 0);
lean_inc(x_69);
lean_dec(x_39);
x_70 = l_Lean_instInhabitedSyntax;
x_71 = l_Array_instInhabited(lean_box(0));
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_get(x_72, x_69, x_36);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_92 = lean_array_get_size(x_69);
x_93 = lean_nat_dec_lt(x_36, x_92);
if (x_93 == 0)
{
lean_dec(x_92);
x_90 = x_34;
goto block_91;
}
else
{
if (x_93 == 0)
{
lean_dec(x_92);
x_90 = x_34;
goto block_91;
}
else
{
size_t x_94; uint8_t x_95; 
x_94 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_95 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3(x_74, x_19, x_34, x_69, x_37, x_94);
x_90 = x_95;
goto block_91;
}
}
block_81:
{
size_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_77 = lean_array_size(x_69);
x_78 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2(x_77, x_37, x_69);
x_79 = lean_unbox(x_11);
x_80 = l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(x_1, x_79, x_15, x_78, x_74, x_75, x_76);
lean_dec(x_75);
lean_dec(x_1);
return x_80;
}
block_89:
{
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_15);
x_83 = lean_mk_string_unchecked("Ambiguous notation in cdot function has different numbers of '·' arguments in each alternative.", 96, 95);
x_84 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_83, x_3, x_40);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
x_75 = x_3;
x_76 = x_40;
goto block_81;
}
}
block_91:
{
if (x_90 == 0)
{
x_82 = x_19;
goto block_89;
}
else
{
x_82 = x_34;
goto block_89;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_38);
if (x_96 == 0)
{
return x_38;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_38, 0);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_38);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_3);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_2);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_4);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_mk_string_unchecked("x", 1, 1);
x_105 = lean_array_get_size(x_2);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_105, x_106);
lean_dec(x_105);
x_108 = l___private_Init_Data_Repr_0__Nat_reprFast(x_107);
x_109 = lean_string_append(x_104, x_108);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = l_Lean_Name_str___override(x_110, x_109);
x_112 = lean_ctor_get(x_3, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 2);
lean_inc(x_113);
lean_dec(x_3);
x_114 = l_Lean_addMacroScope(x_112, x_111, x_113);
x_115 = lean_unbox(x_11);
x_116 = l_Lean_mkIdentFrom(x_1, x_114, x_115);
lean_dec(x_1);
lean_inc(x_116);
x_117 = lean_array_push(x_2, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_4);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_2);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__0(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_go_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; size_t x_9; size_t x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandCDot_x3f_go_spec__3(x_1, x_7, x_8, x_4, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_expandCDot_x3f_go___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_array_uget(x_5, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(x_1, x_2, x_10, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_5, x_4, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_19 = lean_array_uset(x_15, x_4, x_12);
x_4 = x_18;
x_5 = x_19;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Syntax_structEq(x_3, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_array_size(x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2(x_1, x_2, x_16, x_18, x_8, x_4, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_3, 2, x_21);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_3, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_3);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_9, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_27);
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_array_size(x_8);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2(x_1, x_2, x_33, x_35, x_8, x_4, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
lean_ctor_set(x_40, 2, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_43 = x_9;
} else {
 lean_dec_ref(x_9);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_3);
x_46 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
lean_ctor_set(x_46, 0, x_3);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_46, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
lean_ctor_set(x_46, 0, x_54);
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_39; 
x_39 = l_Lean_Elab_Term_hasCDot(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_44, x_45);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 5);
lean_inc(x_53);
lean_dec(x_2);
lean_inc(x_44);
lean_inc(x_50);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_52);
lean_ctor_set(x_54, 5, x_53);
lean_inc(x_54);
x_55 = l_Lean_Elab_Term_expandCDot_x3f_go(x_1, x_43, x_54, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_eq(x_61, x_45);
lean_dec(x_61);
if (x_62 == 0)
{
lean_free_object(x_56);
lean_dec(x_50);
lean_dec(x_44);
x_4 = x_60;
x_5 = x_59;
x_6 = x_54;
x_7 = x_57;
goto block_38;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = lean_mk_string_unchecked("ident", 5, 5);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_box(0);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_65);
lean_ctor_set(x_56, 0, x_64);
x_66 = l_Lean_instInhabitedTSyntax(x_56);
lean_dec(x_56);
x_67 = lean_mk_string_unchecked("x", 1, 1);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = l_Lean_addMacroScope(x_50, x_68, x_44);
x_70 = lean_array_get(x_66, x_60, x_42);
x_71 = l_Lean_mkIdentFrom(x_70, x_69, x_62);
lean_inc(x_71);
x_72 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(x_70, x_71, x_59, x_54, x_57);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_set(x_60, x_42, x_71);
x_4 = x_75;
x_5 = x_73;
x_6 = x_54;
x_7 = x_74;
goto block_38;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_eq(x_78, x_45);
lean_dec(x_78);
if (x_79 == 0)
{
lean_dec(x_50);
lean_dec(x_44);
x_4 = x_77;
x_5 = x_76;
x_6 = x_54;
x_7 = x_57;
goto block_38;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_mk_string_unchecked("ident", 5, 5);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_instInhabitedTSyntax(x_83);
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("x", 1, 1);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = l_Lean_addMacroScope(x_50, x_86, x_44);
x_88 = lean_array_get(x_84, x_77, x_42);
x_89 = l_Lean_mkIdentFrom(x_88, x_87, x_79);
lean_inc(x_89);
x_90 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(x_88, x_89, x_76, x_54, x_57);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_array_set(x_77, x_42, x_89);
x_4 = x_93;
x_5 = x_91;
x_6 = x_54;
x_7 = x_92;
goto block_38;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_44);
x_94 = !lean_is_exclusive(x_55);
if (x_94 == 0)
{
return x_55;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_55, 0);
x_96 = lean_ctor_get(x_55, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_55);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_38:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_8 = lean_ctor_get(x_6, 5);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_SourceInfo_fromRef(x_8, x_10);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_11);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_mk_string_unchecked("basicFun", 8, 8);
x_19 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_18);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Array_mkArray0(lean_box(0));
x_23 = lean_array_size(x_4);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0(x_23, x_25, x_4);
x_27 = lean_array_size(x_26);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_27, x_25, x_26);
lean_inc(x_22);
x_29 = l_Array_append(lean_box(0), x_22, x_28);
lean_dec(x_28);
lean_inc(x_21);
lean_inc(x_11);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_11);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
x_32 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_11);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_11);
x_34 = l_Lean_Syntax_node4(x_11, x_19, x_30, x_31, x_33, x_5);
x_35 = l_Lean_Syntax_node2(x_11, x_16, x_17, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_replaceM___at___Lean_Elab_Term_expandCDot_x3f_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f_expandCDotArg_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("paren", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_expandCDot_x3f(x_12, x_2, x_3);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l_Lean_Syntax_structEq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Lean_Syntax_structEq(x_1, x_5);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_4);
x_6 = l_Lean_Syntax_structEq(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_List_erase___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__2(x_5, x_2);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Syntax_structEq(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_erase___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__2(x_9, x_2);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = l_List_isEmpty___redArg(x_2);
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_6 = l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1(x_4, x_2);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_List_erase___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__2(x_2, x_4);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("byTactic", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCDotFunctionAlias_x3f_expandCDotArg_x3f), 3, 1);
lean_closure_set(x_51, 0, x_1);
lean_inc(x_6);
lean_inc(x_2);
x_52 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0___boxed), 1, 0);
x_64 = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
lean_inc(x_6);
lean_inc(x_2);
x_65 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_87 = lean_mk_string_unchecked("Lean", 4, 4);
x_88 = lean_mk_string_unchecked("Parser", 6, 6);
x_89 = lean_mk_string_unchecked("Term", 4, 4);
x_90 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_91 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_90);
lean_inc(x_66);
x_92 = l_Lean_Syntax_isOfKind(x_66, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_67);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = l_Lean_Syntax_getArg(x_66, x_95);
lean_dec(x_66);
x_97 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_98 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_97);
lean_inc(x_96);
x_99 = l_Lean_Syntax_isOfKind(x_96, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_96);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_67);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Syntax_getArg(x_96, x_95);
x_104 = l_Lean_Syntax_matchesNull(x_103, x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_96);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_67);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = l_Lean_Syntax_getArg(x_96, x_102);
x_108 = lean_unsigned_to_nat(3u);
x_109 = l_Lean_Syntax_getArg(x_96, x_108);
lean_dec(x_96);
x_110 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_111 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_110);
lean_inc(x_109);
x_112 = l_Lean_Syntax_isOfKind(x_109, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_mk_string_unchecked("binop", 5, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_115 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_114);
lean_inc(x_109);
x_116 = l_Lean_Syntax_isOfKind(x_109, x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_mk_string_unchecked("binop_lazy", 10, 10);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_118 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_117);
lean_inc(x_109);
x_119 = l_Lean_Syntax_isOfKind(x_109, x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_mk_string_unchecked("leftact", 7, 7);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_121 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_120);
lean_inc(x_109);
x_122 = l_Lean_Syntax_isOfKind(x_109, x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_mk_string_unchecked("rightact", 8, 8);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_124 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_123);
lean_inc(x_109);
x_125 = l_Lean_Syntax_isOfKind(x_109, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_mk_string_unchecked("binrel", 6, 6);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_127 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_126);
lean_inc(x_109);
x_128 = l_Lean_Syntax_isOfKind(x_109, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_61);
x_129 = lean_mk_string_unchecked("binrel_no_prop", 14, 14);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_130 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_129);
lean_inc(x_109);
x_131 = l_Lean_Syntax_isOfKind(x_109, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_68);
x_132 = lean_mk_string_unchecked("unop", 4, 4);
x_133 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_132);
lean_inc(x_109);
x_134 = l_Lean_Syntax_isOfKind(x_109, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_67);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; size_t x_152; size_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_137 = l_Lean_Syntax_getArg(x_109, x_95);
x_138 = lean_mk_string_unchecked("term", 4, 4);
x_148 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_149 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_150 = lean_mk_empty_array_with_capacity(x_95);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_array_size(x_151);
x_153 = lean_usize_of_nat(x_102);
x_154 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_152, x_153, x_151);
x_155 = lean_array_get_size(x_149);
x_156 = lean_array_get_size(x_154);
x_157 = lean_nat_dec_eq(x_155, x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_149);
x_139 = x_131;
goto block_147;
}
else
{
uint8_t x_158; 
x_158 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_149, x_154, x_155);
lean_dec(x_154);
lean_dec(x_149);
x_139 = x_158;
goto block_147;
}
block_147:
{
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_67);
return x_141;
}
else
{
lean_object* x_142; 
x_142 = l_Lean_Elab_Term_resolveId_x3f(x_137, x_138, x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_138);
if (lean_obj_tag(x_142) == 0)
{
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = l_Lean_Exception_isInterrupt(x_143);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Exception_isRuntime(x_143);
lean_dec(x_143);
x_9 = x_142;
x_10 = x_144;
x_11 = x_146;
goto block_14;
}
else
{
lean_dec(x_143);
x_9 = x_142;
x_10 = x_144;
x_11 = x_145;
goto block_14;
}
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_182; lean_object* x_183; lean_object* x_184; size_t x_185; size_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
x_159 = l_Lean_Syntax_getArg(x_109, x_95);
x_160 = lean_mk_string_unchecked("term", 4, 4);
x_167 = l_Lean_Syntax_getArg(x_109, x_108);
x_168 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_169 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_182 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_168);
x_183 = lean_array_push(x_182, x_168);
lean_inc(x_167);
x_184 = lean_array_push(x_183, x_167);
x_185 = lean_array_size(x_184);
x_186 = lean_usize_of_nat(x_102);
x_187 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_185, x_186, x_184);
x_188 = lean_array_get_size(x_169);
x_189 = lean_array_get_size(x_187);
x_190 = lean_nat_dec_eq(x_188, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_dec(x_188);
lean_dec(x_187);
x_170 = x_128;
goto block_181;
}
else
{
uint8_t x_191; 
x_191 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_169, x_187, x_188);
lean_dec(x_187);
x_170 = x_191;
goto block_181;
}
block_166:
{
lean_object* x_161; 
x_161 = l_Lean_Elab_Term_resolveId_x3f(x_159, x_160, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_160);
if (lean_obj_tag(x_161) == 0)
{
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
x_164 = l_Lean_Exception_isInterrupt(x_162);
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = l_Lean_Exception_isRuntime(x_162);
lean_dec(x_162);
x_15 = x_163;
x_16 = x_161;
x_17 = x_165;
goto block_20;
}
else
{
lean_dec(x_162);
x_15 = x_163;
x_16 = x_161;
x_17 = x_164;
goto block_20;
}
}
}
block_181:
{
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_171 = lean_mk_empty_array_with_capacity(x_113);
x_172 = lean_array_push(x_171, x_167);
x_173 = lean_array_push(x_172, x_168);
x_174 = lean_array_size(x_173);
x_175 = lean_usize_of_nat(x_102);
x_176 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_174, x_175, x_173);
x_177 = lean_array_get_size(x_169);
x_178 = lean_array_get_size(x_176);
x_179 = lean_nat_dec_eq(x_177, x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_71;
}
else
{
uint8_t x_180; 
x_180 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_169, x_176, x_177);
lean_dec(x_176);
lean_dec(x_169);
if (x_180 == 0)
{
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_71;
}
else
{
lean_dec(x_68);
goto block_166;
}
}
}
else
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_68);
goto block_166;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_215; lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
x_192 = l_Lean_Syntax_getArg(x_109, x_95);
x_193 = lean_mk_string_unchecked("term", 4, 4);
x_200 = l_Lean_Syntax_getArg(x_109, x_108);
x_201 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_202 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_215 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_201);
x_216 = lean_array_push(x_215, x_201);
lean_inc(x_200);
x_217 = lean_array_push(x_216, x_200);
x_218 = lean_array_size(x_217);
x_219 = lean_usize_of_nat(x_102);
x_220 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_218, x_219, x_217);
x_221 = lean_array_get_size(x_202);
x_222 = lean_array_get_size(x_220);
x_223 = lean_nat_dec_eq(x_221, x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
x_203 = x_125;
goto block_214;
}
else
{
uint8_t x_224; 
x_224 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_202, x_220, x_221);
lean_dec(x_220);
x_203 = x_224;
goto block_214;
}
block_199:
{
lean_object* x_194; 
x_194 = l_Lean_Elab_Term_resolveId_x3f(x_192, x_193, x_125, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
x_197 = l_Lean_Exception_isInterrupt(x_195);
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = l_Lean_Exception_isRuntime(x_195);
lean_dec(x_195);
x_21 = x_194;
x_22 = x_196;
x_23 = x_198;
goto block_26;
}
else
{
lean_dec(x_195);
x_21 = x_194;
x_22 = x_196;
x_23 = x_197;
goto block_26;
}
}
}
block_214:
{
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; size_t x_207; size_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_204 = lean_mk_empty_array_with_capacity(x_113);
x_205 = lean_array_push(x_204, x_200);
x_206 = lean_array_push(x_205, x_201);
x_207 = lean_array_size(x_206);
x_208 = lean_usize_of_nat(x_102);
x_209 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_207, x_208, x_206);
x_210 = lean_array_get_size(x_202);
x_211 = lean_array_get_size(x_209);
x_212 = lean_nat_dec_eq(x_210, x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_202);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_74;
}
else
{
uint8_t x_213; 
x_213 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_202, x_209, x_210);
lean_dec(x_209);
lean_dec(x_202);
if (x_213 == 0)
{
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_74;
}
else
{
lean_dec(x_61);
goto block_199;
}
}
}
else
{
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_61);
goto block_199;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_248; lean_object* x_249; lean_object* x_250; size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
x_225 = l_Lean_Syntax_getArg(x_109, x_95);
x_226 = lean_mk_string_unchecked("term", 4, 4);
x_233 = l_Lean_Syntax_getArg(x_109, x_108);
x_234 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_235 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_248 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_234);
x_249 = lean_array_push(x_248, x_234);
lean_inc(x_233);
x_250 = lean_array_push(x_249, x_233);
x_251 = lean_array_size(x_250);
x_252 = lean_usize_of_nat(x_102);
x_253 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_251, x_252, x_250);
x_254 = lean_array_get_size(x_235);
x_255 = lean_array_get_size(x_253);
x_256 = lean_nat_dec_eq(x_254, x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_dec(x_254);
lean_dec(x_253);
x_236 = x_122;
goto block_247;
}
else
{
uint8_t x_257; 
x_257 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_235, x_253, x_254);
lean_dec(x_253);
x_236 = x_257;
goto block_247;
}
block_232:
{
lean_object* x_227; 
x_227 = l_Lean_Elab_Term_resolveId_x3f(x_225, x_226, x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_226);
if (lean_obj_tag(x_227) == 0)
{
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
x_230 = l_Lean_Exception_isInterrupt(x_228);
if (x_230 == 0)
{
uint8_t x_231; 
x_231 = l_Lean_Exception_isRuntime(x_228);
lean_dec(x_228);
x_27 = x_227;
x_28 = x_229;
x_29 = x_231;
goto block_32;
}
else
{
lean_dec(x_228);
x_27 = x_227;
x_28 = x_229;
x_29 = x_230;
goto block_32;
}
}
}
block_247:
{
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_237 = lean_mk_empty_array_with_capacity(x_113);
x_238 = lean_array_push(x_237, x_233);
x_239 = lean_array_push(x_238, x_234);
x_240 = lean_array_size(x_239);
x_241 = lean_usize_of_nat(x_102);
x_242 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_240, x_241, x_239);
x_243 = lean_array_get_size(x_235);
x_244 = lean_array_get_size(x_242);
x_245 = lean_nat_dec_eq(x_243, x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_77;
}
else
{
uint8_t x_246; 
x_246 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_235, x_242, x_243);
lean_dec(x_242);
lean_dec(x_235);
if (x_246 == 0)
{
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_77;
}
else
{
goto block_232;
}
}
}
else
{
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
goto block_232;
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_281; lean_object* x_282; lean_object* x_283; size_t x_284; size_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
x_258 = l_Lean_Syntax_getArg(x_109, x_95);
x_259 = lean_mk_string_unchecked("term", 4, 4);
x_266 = l_Lean_Syntax_getArg(x_109, x_108);
x_267 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_268 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_281 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_267);
x_282 = lean_array_push(x_281, x_267);
lean_inc(x_266);
x_283 = lean_array_push(x_282, x_266);
x_284 = lean_array_size(x_283);
x_285 = lean_usize_of_nat(x_102);
x_286 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_284, x_285, x_283);
x_287 = lean_array_get_size(x_268);
x_288 = lean_array_get_size(x_286);
x_289 = lean_nat_dec_eq(x_287, x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_dec(x_287);
lean_dec(x_286);
x_269 = x_119;
goto block_280;
}
else
{
uint8_t x_290; 
x_290 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_268, x_286, x_287);
lean_dec(x_286);
x_269 = x_290;
goto block_280;
}
block_265:
{
lean_object* x_260; 
x_260 = l_Lean_Elab_Term_resolveId_x3f(x_258, x_259, x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_259);
if (lean_obj_tag(x_260) == 0)
{
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
x_263 = l_Lean_Exception_isInterrupt(x_261);
if (x_263 == 0)
{
uint8_t x_264; 
x_264 = l_Lean_Exception_isRuntime(x_261);
lean_dec(x_261);
x_33 = x_262;
x_34 = x_260;
x_35 = x_264;
goto block_38;
}
else
{
lean_dec(x_261);
x_33 = x_262;
x_34 = x_260;
x_35 = x_263;
goto block_38;
}
}
}
block_280:
{
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; size_t x_273; size_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_270 = lean_mk_empty_array_with_capacity(x_113);
x_271 = lean_array_push(x_270, x_266);
x_272 = lean_array_push(x_271, x_267);
x_273 = lean_array_size(x_272);
x_274 = lean_usize_of_nat(x_102);
x_275 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_273, x_274, x_272);
x_276 = lean_array_get_size(x_268);
x_277 = lean_array_get_size(x_275);
x_278 = lean_nat_dec_eq(x_276, x_277);
lean_dec(x_277);
if (x_278 == 0)
{
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_268);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_80;
}
else
{
uint8_t x_279; 
x_279 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_268, x_275, x_276);
lean_dec(x_275);
lean_dec(x_268);
if (x_279 == 0)
{
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_80;
}
else
{
goto block_265;
}
}
}
else
{
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
goto block_265;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_314; lean_object* x_315; lean_object* x_316; size_t x_317; size_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
x_291 = l_Lean_Syntax_getArg(x_109, x_95);
x_292 = lean_mk_string_unchecked("term", 4, 4);
x_299 = l_Lean_Syntax_getArg(x_109, x_108);
x_300 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_301 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_314 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_300);
x_315 = lean_array_push(x_314, x_300);
lean_inc(x_299);
x_316 = lean_array_push(x_315, x_299);
x_317 = lean_array_size(x_316);
x_318 = lean_usize_of_nat(x_102);
x_319 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_317, x_318, x_316);
x_320 = lean_array_get_size(x_301);
x_321 = lean_array_get_size(x_319);
x_322 = lean_nat_dec_eq(x_320, x_321);
lean_dec(x_321);
if (x_322 == 0)
{
lean_dec(x_320);
lean_dec(x_319);
x_302 = x_116;
goto block_313;
}
else
{
uint8_t x_323; 
x_323 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_301, x_319, x_320);
lean_dec(x_319);
x_302 = x_323;
goto block_313;
}
block_298:
{
lean_object* x_293; 
x_293 = l_Lean_Elab_Term_resolveId_x3f(x_291, x_292, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_292);
if (lean_obj_tag(x_293) == 0)
{
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
x_296 = l_Lean_Exception_isInterrupt(x_294);
if (x_296 == 0)
{
uint8_t x_297; 
x_297 = l_Lean_Exception_isRuntime(x_294);
lean_dec(x_294);
x_39 = x_293;
x_40 = x_295;
x_41 = x_297;
goto block_44;
}
else
{
lean_dec(x_294);
x_39 = x_293;
x_40 = x_295;
x_41 = x_296;
goto block_44;
}
}
}
block_313:
{
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; size_t x_306; size_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_303 = lean_mk_empty_array_with_capacity(x_113);
x_304 = lean_array_push(x_303, x_299);
x_305 = lean_array_push(x_304, x_300);
x_306 = lean_array_size(x_305);
x_307 = lean_usize_of_nat(x_102);
x_308 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_306, x_307, x_305);
x_309 = lean_array_get_size(x_301);
x_310 = lean_array_get_size(x_308);
x_311 = lean_nat_dec_eq(x_309, x_310);
lean_dec(x_310);
if (x_311 == 0)
{
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_301);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_83;
}
else
{
uint8_t x_312; 
x_312 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_301, x_308, x_309);
lean_dec(x_308);
lean_dec(x_301);
if (x_312 == 0)
{
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_83;
}
else
{
goto block_298;
}
}
}
else
{
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
goto block_298;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_347; lean_object* x_348; lean_object* x_349; size_t x_350; size_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
x_324 = l_Lean_Syntax_getArg(x_109, x_95);
x_325 = lean_mk_string_unchecked("term", 4, 4);
x_332 = l_Lean_Syntax_getArg(x_109, x_108);
x_333 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_334 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_347 = lean_mk_empty_array_with_capacity(x_113);
lean_inc(x_333);
x_348 = lean_array_push(x_347, x_333);
lean_inc(x_332);
x_349 = lean_array_push(x_348, x_332);
x_350 = lean_array_size(x_349);
x_351 = lean_usize_of_nat(x_102);
x_352 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_350, x_351, x_349);
x_353 = lean_array_get_size(x_334);
x_354 = lean_array_get_size(x_352);
x_355 = lean_nat_dec_eq(x_353, x_354);
lean_dec(x_354);
if (x_355 == 0)
{
lean_dec(x_353);
lean_dec(x_352);
x_335 = x_112;
goto block_346;
}
else
{
uint8_t x_356; 
x_356 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_334, x_352, x_353);
lean_dec(x_352);
x_335 = x_356;
goto block_346;
}
block_331:
{
lean_object* x_326; 
x_326 = l_Lean_Elab_Term_resolveId_x3f(x_324, x_325, x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_325);
if (lean_obj_tag(x_326) == 0)
{
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
x_329 = l_Lean_Exception_isInterrupt(x_327);
if (x_329 == 0)
{
uint8_t x_330; 
x_330 = l_Lean_Exception_isRuntime(x_327);
lean_dec(x_327);
x_45 = x_326;
x_46 = x_328;
x_47 = x_330;
goto block_50;
}
else
{
lean_dec(x_327);
x_45 = x_326;
x_46 = x_328;
x_47 = x_329;
goto block_50;
}
}
}
block_346:
{
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; size_t x_339; size_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_336 = lean_mk_empty_array_with_capacity(x_113);
x_337 = lean_array_push(x_336, x_332);
x_338 = lean_array_push(x_337, x_333);
x_339 = lean_array_size(x_338);
x_340 = lean_usize_of_nat(x_102);
x_341 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandCDot_x3f_spec__1(x_339, x_340, x_338);
x_342 = lean_array_get_size(x_334);
x_343 = lean_array_get_size(x_341);
x_344 = lean_nat_dec_eq(x_342, x_343);
lean_dec(x_343);
if (x_344 == 0)
{
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_86;
}
else
{
uint8_t x_345; 
x_345 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_334, x_341, x_342);
lean_dec(x_341);
lean_dec(x_334);
if (x_345 == 0)
{
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_86;
}
else
{
goto block_331;
}
}
}
else
{
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
goto block_331;
}
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_68);
lean_dec(x_61);
x_357 = l_Lean_Syntax_getArg(x_109, x_95);
x_358 = l_Lean_Syntax_getArgs(x_357);
lean_dec(x_357);
x_359 = l_Lean_Syntax_getArgs(x_107);
lean_dec(x_107);
x_360 = lean_array_to_list(x_359);
x_361 = lean_array_to_list(x_358);
x_362 = l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1(x_360, x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_109);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_363 = lean_box(0);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_67);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; 
x_365 = lean_mk_string_unchecked("term", 4, 4);
x_366 = l_Lean_Syntax_getArg(x_109, x_102);
lean_dec(x_109);
x_367 = lean_box(0);
x_368 = lean_unbox(x_367);
x_369 = l_Lean_Elab_Term_resolveId_x3f(x_366, x_365, x_368, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_6);
lean_dec(x_365);
if (lean_obj_tag(x_369) == 0)
{
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_380; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
x_380 = l_Lean_Exception_isInterrupt(x_370);
if (x_380 == 0)
{
uint8_t x_381; 
x_381 = l_Lean_Exception_isRuntime(x_370);
lean_dec(x_370);
x_372 = x_381;
goto block_379;
}
else
{
lean_dec(x_370);
x_372 = x_380;
goto block_379;
}
block_379:
{
if (x_372 == 0)
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_369);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_369, 1);
lean_dec(x_374);
x_375 = lean_ctor_get(x_369, 0);
lean_dec(x_375);
x_376 = lean_box(0);
lean_ctor_set_tag(x_369, 0);
lean_ctor_set(x_369, 0, x_376);
return x_369;
}
else
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_369);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_371);
return x_378;
}
}
else
{
lean_dec(x_371);
return x_369;
}
}
}
}
}
}
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
block_74:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_61;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
block_77:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_67);
return x_76;
}
block_80:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_67);
return x_79;
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_67);
return x_82;
}
block_86:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_67);
return x_85;
}
}
else
{
uint8_t x_382; 
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_65);
if (x_382 == 0)
{
return x_65;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_65, 0);
x_384 = lean_ctor_get(x_65, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_65);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_386 = !lean_is_exclusive(x_52);
if (x_386 == 0)
{
return x_52;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_52, 0);
x_388 = lean_ctor_get(x_52, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_52);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
block_14:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_dec(x_10);
return x_9;
}
}
block_20:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_dec(x_15);
return x_16;
}
}
block_26:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_dec(x_22);
return x_21;
}
}
block_32:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_dec(x_28);
return x_27;
}
}
block_38:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
lean_dec(x_33);
return x_34;
}
}
block_44:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_dec(x_40);
return x_39;
}
}
block_50:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_dec(x_46);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1_spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isPerm___at___Lean_Elab_Term_elabCDotFunctionAlias_x3f_spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandParen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("paren", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_expandCDot_x3f(x_12, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
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
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandParen__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandParen", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandParen), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandParen_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandParen", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(297u);
x_8 = lean_unsigned_to_nat(40u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(299u);
x_11 = lean_unsigned_to_nat(37u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(44u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(55u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("tuple", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(3u);
lean_inc(x_13);
x_16 = l_Lean_Syntax_matchesNull(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getArg(x_13, x_11);
lean_dec(x_13);
x_22 = lean_mk_empty_array_with_capacity(x_12);
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_Syntax_TSepArray_getElems___redArg(x_20);
lean_dec(x_20);
x_25 = l_Array_append(lean_box(0), x_23, x_24);
lean_dec(x_24);
lean_inc(x_2);
x_26 = l_Lean_Elab_Term_mkPairs(x_25, x_2, x_3);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l_Lean_Elab_Term_expandCDot_x3f(x_27, x_2, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_SourceInfo_fromRef(x_45, x_47);
lean_dec(x_45);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_mk_string_unchecked("Unit.unit", 9, 9);
x_52 = l_String_toSubstring_x27(x_51);
x_53 = lean_mk_string_unchecked("Unit", 4, 4);
x_54 = lean_mk_string_unchecked("unit", 4, 4);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
lean_inc(x_55);
x_56 = l_Lean_addMacroScope(x_50, x_55, x_49);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTuple__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("tuple", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandTuple", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTuple), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTuple_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandTuple", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(301u);
x_8 = lean_unsigned_to_nat(40u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(306u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(44u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(55u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandTypeAscription(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_24; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_24 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_1);
x_25 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_26 = lean_unsigned_to_nat(1u);
x_55 = lean_unsigned_to_nat(3u);
x_56 = l_Lean_Syntax_getArg(x_1, x_55);
x_57 = l_Lean_Syntax_getOptional_x3f(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
x_27 = x_58;
goto block_54;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
x_27 = x_57;
goto block_54;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_27 = x_61;
goto block_54;
}
}
block_54:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Syntax_getArg(x_1, x_26);
lean_dec(x_1);
lean_inc(x_2);
x_29 = l_Lean_Elab_Term_expandCDot_x3f(x_28, x_2, x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_8);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_31);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_2, 5);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_SourceInfo_fromRef(x_35, x_37);
lean_dec(x_35);
x_39 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_38);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_38);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("null", 4, 4);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_46; 
x_46 = l_Array_empty(lean_box(0));
x_9 = x_40;
x_10 = x_38;
x_11 = x_34;
x_12 = x_42;
x_13 = x_44;
x_14 = x_45;
x_15 = x_33;
x_16 = x_46;
goto block_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
lean_inc(x_47);
lean_dec(x_27);
x_48 = l_Array_empty(lean_box(0));
x_49 = lean_array_push(x_48, x_47);
x_9 = x_40;
x_10 = x_38;
x_11 = x_34;
x_12 = x_42;
x_13 = x_44;
x_14 = x_45;
x_15 = x_33;
x_16 = x_49;
goto block_23;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Array_append(lean_box(0), x_14, x_16);
lean_dec(x_16);
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_10);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Syntax_node5(x_10, x_8, x_9, x_11, x_12, x_18, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTypeAscription__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandTypeAscription", 20, 20);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandTypeAscription), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandTypeAscription_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandTypeAscription", 20, 20);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(308u);
x_8 = lean_unsigned_to_nat(49u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(313u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(53u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(73u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeAscription(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("typeAscription", 14, 14);
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
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
lean_inc(x_21);
x_22 = l_Lean_Syntax_matchesNull(x_21, x_18);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Syntax_matchesNull(x_21, x_17);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_box(0);
x_26 = lean_box(x_15);
x_27 = lean_box(x_15);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_28, 0, x_19);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_28, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Term_ensureHasType(x_2, x_32, x_34, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
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
return x_31;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_dec(x_2);
x_36 = l_Lean_Syntax_getArg(x_21, x_17);
lean_dec(x_21);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_37, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_43);
x_44 = l_Lean_Elab_Term_elabTerm(x_19, x_43, x_15, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Term_ensureHasType(x_43, x_45, x_47, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_49;
}
else
{
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
}
else
{
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeAscription__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabTypeAscription", 18, 18);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeAscription), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeAscription_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabTypeAscription", 18, 18);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(315u);
x_8 = lean_unsigned_to_nat(36u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(323u);
x_11 = lean_unsigned_to_nat(34u);
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
x_16 = lean_unsigned_to_nat(58u);
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
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_33 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0___boxed), 1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_2);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(8u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_36, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = l_Nat_nextPowerOfTwo(x_41);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = lean_mk_array(x_42, x_43);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_37);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_35);
x_46 = l_Lean_Expr_hasFVar(x_1);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_1);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_9 = x_47;
x_10 = x_35;
goto block_26;
}
else
{
lean_object* x_48; 
lean_dec(x_35);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_48;
goto block_32;
}
}
else
{
lean_object* x_49; 
lean_dec(x_35);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_49;
goto block_32;
}
block_26:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_take(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 4);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_9);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_9 = x_31;
x_10 = x_30;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_68; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
x_74 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0___boxed), 1, 0);
x_75 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_75, 0, x_2);
x_76 = lean_ctor_get(x_50, 0);
lean_inc(x_76);
lean_dec(x_50);
x_77 = lean_unsigned_to_nat(8u);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_77, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = l_Nat_nextPowerOfTwo(x_82);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_88 = l_Lean_Expr_hasFVar(x_1);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasMVar(x_1);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_1);
x_52 = x_89;
x_53 = x_76;
goto block_67;
}
else
{
lean_object* x_90; 
lean_dec(x_76);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_90;
goto block_73;
}
}
else
{
lean_object* x_91; 
lean_dec(x_76);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_91;
goto block_73;
}
block_67:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_st_ref_take(x_3, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_st_ref_set(x_3, x_61, x_56);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(x_52);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_52 = x_72;
x_53 = x_71;
goto block_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Expr_fvarId_x21(x_1);
x_12 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg(x_2, x_11, x_4, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(x_8);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = lean_unbox(x_12);
x_15 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_1, x_13, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_mkIdentFrom(x_1, x_2, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = lean_apply_8(x_4, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_array_push(x_19, x_6);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Meta_mkLambdaFVars(x_20, x_16, x_3, x_5, x_3, x_22, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
return x_23;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isFVar(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_mk_string_unchecked("h", 1, 1);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_13, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_17 = lean_infer_type(x_2, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(1);
x_21 = lean_box(x_11);
lean_inc(x_15);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0___boxed), 13, 5);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_20);
x_23 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(x_15, x_18, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Expr_app___override(x_25, x_2);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l_Lean_Expr_app___override(x_27, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_dec(x_2);
return x_23;
}
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_apply_8(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor___lam__0(x_1, x_2, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_mk_empty_array_with_capacity(x_1);
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_array_push(x_15, x_6);
x_17 = lean_expr_instantiate1(x_3, x_2);
lean_dec(x_2);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_17, x_4, x_5, x_4, x_19, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_mk_string_unchecked("h", 1, 1);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_15, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_19 = l_Lean_Meta_mkEq(x_1, x_6, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(x_4);
x_23 = lean_box(x_5);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__0___boxed), 13, 5);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_22);
lean_closure_set(x_24, 4, x_23);
x_25 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(x_17, x_20, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_25;
}
else
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_mk_string_unchecked("x", 1, 1);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_15, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_2);
x_20 = lean_box(x_3);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__1___boxed), 13, 5);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_6);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_20);
x_22 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(x_17, x_4, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = lean_apply_9(x_1, x_5, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
x_18 = l_Lean_Meta_isTypeCorrect(x_16, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked("invalid `▸` notation, failed to compute motive for the substitution", 69, 67);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_Meta_mkEqRec(x_16, x_2, x_4, x_10, x_11, x_12, x_13, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
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
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_st_ref_get(x_16, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 5);
lean_inc(x_22);
x_23 = l_Lean_SourceInfo_fromRef(x_22, x_1);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_24);
x_26 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_23);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_23);
x_27 = lean_mk_string_unchecked("Tactic", 6, 6);
x_28 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_27);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Name_mkStr4(x_2, x_3, x_27, x_28);
x_30 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_27);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Name_mkStr4(x_2, x_3, x_27, x_30);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
lean_inc(x_5);
lean_inc(x_27);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Name_mkStr4(x_2, x_3, x_27, x_5);
lean_inc(x_23);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_5);
lean_inc(x_33);
lean_inc(x_23);
x_36 = l_Lean_Syntax_node1(x_23, x_33, x_6);
lean_inc(x_23);
x_37 = l_Lean_Syntax_node2(x_23, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_23);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_40);
x_41 = l_Lean_Name_mkStr4(x_2, x_3, x_27, x_40);
lean_inc(x_23);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_40);
lean_inc(x_23);
x_43 = l_Lean_Syntax_node2(x_23, x_41, x_42, x_10);
lean_inc(x_23);
x_44 = l_Lean_Syntax_node3(x_23, x_33, x_37, x_39, x_43);
lean_inc(x_23);
x_45 = l_Lean_Syntax_node1(x_23, x_31, x_44);
lean_inc(x_23);
x_46 = l_Lean_Syntax_node1(x_23, x_29, x_45);
x_47 = l_Lean_Syntax_node2(x_23, x_25, x_18, x_46);
x_48 = lean_box(x_8);
x_49 = lean_box(x_8);
lean_inc(x_47);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_50, 0, x_47);
lean_closure_set(x_50, 1, x_7);
lean_closure_set(x_50, 2, x_48);
lean_closure_set(x_50, 3, x_49);
x_51 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_9, x_47, x_50, x_11, x_12, x_13, x_14, x_15, x_16, x_20);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_ctor_get(x_15, 5);
lean_inc(x_53);
x_54 = l_Lean_SourceInfo_fromRef(x_53, x_1);
lean_dec(x_53);
x_55 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_55);
x_57 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_54);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("Tactic", 6, 6);
x_60 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_59);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_Name_mkStr4(x_2, x_3, x_59, x_60);
x_62 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_59);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_Name_mkStr4(x_2, x_3, x_59, x_62);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
lean_inc(x_5);
lean_inc(x_59);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Name_mkStr4(x_2, x_3, x_59, x_5);
lean_inc(x_54);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_54);
lean_ctor_set(x_67, 1, x_5);
lean_inc(x_65);
lean_inc(x_54);
x_68 = l_Lean_Syntax_node1(x_54, x_65, x_6);
lean_inc(x_54);
x_69 = l_Lean_Syntax_node2(x_54, x_66, x_67, x_68);
x_70 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_54);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_72);
x_73 = l_Lean_Name_mkStr4(x_2, x_3, x_59, x_72);
lean_inc(x_54);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_72);
lean_inc(x_54);
x_75 = l_Lean_Syntax_node2(x_54, x_73, x_74, x_10);
lean_inc(x_54);
x_76 = l_Lean_Syntax_node3(x_54, x_65, x_69, x_71, x_75);
lean_inc(x_54);
x_77 = l_Lean_Syntax_node1(x_54, x_63, x_76);
lean_inc(x_54);
x_78 = l_Lean_Syntax_node1(x_54, x_61, x_77);
x_79 = l_Lean_Syntax_node2(x_54, x_56, x_58, x_78);
x_80 = lean_box(x_8);
x_81 = lean_box(x_8);
lean_inc(x_79);
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_82, 0, x_79);
lean_closure_set(x_82, 1, x_7);
lean_closure_set(x_82, 2, x_80);
lean_closure_set(x_82, 3, x_81);
x_83 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_9, x_79, x_82, x_11, x_12, x_13, x_14, x_15, x_16, x_52);
return x_83;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_1, x_16, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_20);
lean_dec(x_11);
x_25 = lean_box(x_24);
x_26 = lean_box(x_7);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__4___boxed), 17, 9);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_5);
lean_closure_set(x_27, 5, x_12);
lean_closure_set(x_27, 6, x_6);
lean_closure_set(x_27, 7, x_26);
lean_closure_set(x_27, 8, x_8);
x_28 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor(x_9, x_22, x_27, x_13, x_14, x_15, x_16, x_17, x_18, x_23);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_9);
x_29 = lean_st_ref_get(x_18, x_23);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_17, 5);
lean_inc(x_33);
x_34 = l_Lean_SourceInfo_fromRef(x_33, x_10);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_35);
x_37 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_34);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_34);
x_38 = lean_mk_string_unchecked("Tactic", 6, 6);
x_39 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_38);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Lean_Name_mkStr4(x_2, x_3, x_38, x_39);
x_41 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_38);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Name_mkStr4(x_2, x_3, x_38, x_41);
x_43 = lean_mk_string_unchecked("null", 4, 4);
x_44 = l_Lean_Name_mkStr1(x_43);
lean_inc(x_5);
lean_inc(x_38);
lean_inc(x_3);
lean_inc(x_2);
x_45 = l_Lean_Name_mkStr4(x_2, x_3, x_38, x_5);
lean_inc(x_34);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 0, x_34);
lean_inc(x_44);
lean_inc(x_34);
x_46 = l_Lean_Syntax_node1(x_34, x_44, x_12);
lean_inc(x_34);
x_47 = l_Lean_Syntax_node2(x_34, x_45, x_20, x_46);
x_48 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_34);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_50);
x_51 = l_Lean_Name_mkStr4(x_2, x_3, x_38, x_50);
lean_inc(x_34);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_34);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_34);
x_53 = l_Lean_Syntax_node2(x_34, x_51, x_52, x_11);
lean_inc(x_34);
x_54 = l_Lean_Syntax_node3(x_34, x_44, x_47, x_49, x_53);
lean_inc(x_34);
x_55 = l_Lean_Syntax_node1(x_34, x_42, x_54);
lean_inc(x_34);
x_56 = l_Lean_Syntax_node1(x_34, x_40, x_55);
x_57 = l_Lean_Syntax_node2(x_34, x_36, x_29, x_56);
x_58 = lean_box(x_7);
x_59 = lean_box(x_7);
lean_inc(x_57);
x_60 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_60, 0, x_57);
lean_closure_set(x_60, 1, x_6);
lean_closure_set(x_60, 2, x_58);
lean_closure_set(x_60, 3, x_59);
x_61 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_8, x_57, x_60, x_13, x_14, x_15, x_16, x_17, x_18, x_31);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_dec(x_29);
x_63 = lean_ctor_get(x_17, 5);
lean_inc(x_63);
x_64 = l_Lean_SourceInfo_fromRef(x_63, x_10);
lean_dec(x_63);
x_65 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_65);
x_67 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_64);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("Tactic", 6, 6);
x_70 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_69);
lean_inc(x_3);
lean_inc(x_2);
x_71 = l_Lean_Name_mkStr4(x_2, x_3, x_69, x_70);
x_72 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_69);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l_Lean_Name_mkStr4(x_2, x_3, x_69, x_72);
x_74 = lean_mk_string_unchecked("null", 4, 4);
x_75 = l_Lean_Name_mkStr1(x_74);
lean_inc(x_5);
lean_inc(x_69);
lean_inc(x_3);
lean_inc(x_2);
x_76 = l_Lean_Name_mkStr4(x_2, x_3, x_69, x_5);
lean_inc(x_64);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 0, x_64);
lean_inc(x_75);
lean_inc(x_64);
x_77 = l_Lean_Syntax_node1(x_64, x_75, x_12);
lean_inc(x_64);
x_78 = l_Lean_Syntax_node2(x_64, x_76, x_20, x_77);
x_79 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_64);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_64);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_81);
x_82 = l_Lean_Name_mkStr4(x_2, x_3, x_69, x_81);
lean_inc(x_64);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_81);
lean_inc(x_64);
x_84 = l_Lean_Syntax_node2(x_64, x_82, x_83, x_11);
lean_inc(x_64);
x_85 = l_Lean_Syntax_node3(x_64, x_75, x_78, x_80, x_84);
lean_inc(x_64);
x_86 = l_Lean_Syntax_node1(x_64, x_73, x_85);
lean_inc(x_64);
x_87 = l_Lean_Syntax_node1(x_64, x_71, x_86);
x_88 = l_Lean_Syntax_node2(x_64, x_66, x_68, x_87);
x_89 = lean_box(x_7);
x_90 = lean_box(x_7);
lean_inc(x_88);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_91, 0, x_88);
lean_closure_set(x_91, 1, x_6);
lean_closure_set(x_91, 2, x_89);
lean_closure_set(x_91, 3, x_90);
x_92 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_8, x_88, x_91, x_13, x_14, x_15, x_16, x_17, x_18, x_62);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_20, 0);
x_94 = lean_ctor_get(x_20, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_20);
x_95 = l_Lean_Expr_hasMVar(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_11);
x_96 = lean_box(x_95);
x_97 = lean_box(x_7);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__4___boxed), 17, 9);
lean_closure_set(x_98, 0, x_96);
lean_closure_set(x_98, 1, x_2);
lean_closure_set(x_98, 2, x_3);
lean_closure_set(x_98, 3, x_4);
lean_closure_set(x_98, 4, x_5);
lean_closure_set(x_98, 5, x_12);
lean_closure_set(x_98, 6, x_6);
lean_closure_set(x_98, 7, x_97);
lean_closure_set(x_98, 8, x_8);
x_99 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor(x_9, x_93, x_98, x_13, x_14, x_15, x_16, x_17, x_18, x_94);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_93);
lean_dec(x_9);
x_100 = lean_st_ref_get(x_18, x_94);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_17, 5);
lean_inc(x_103);
x_104 = l_Lean_SourceInfo_fromRef(x_103, x_10);
lean_dec(x_103);
x_105 = lean_mk_string_unchecked("byTactic", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_106 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_105);
x_107 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_104);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(2, 2, 0);
} else {
 x_108 = x_102;
 lean_ctor_set_tag(x_108, 2);
}
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("Tactic", 6, 6);
x_110 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_109);
lean_inc(x_3);
lean_inc(x_2);
x_111 = l_Lean_Name_mkStr4(x_2, x_3, x_109, x_110);
x_112 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_109);
lean_inc(x_3);
lean_inc(x_2);
x_113 = l_Lean_Name_mkStr4(x_2, x_3, x_109, x_112);
x_114 = lean_mk_string_unchecked("null", 4, 4);
x_115 = l_Lean_Name_mkStr1(x_114);
lean_inc(x_5);
lean_inc(x_109);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_Name_mkStr4(x_2, x_3, x_109, x_5);
lean_inc(x_104);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_104);
lean_ctor_set(x_117, 1, x_5);
lean_inc(x_115);
lean_inc(x_104);
x_118 = l_Lean_Syntax_node1(x_104, x_115, x_12);
lean_inc(x_104);
x_119 = l_Lean_Syntax_node2(x_104, x_116, x_117, x_118);
x_120 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_104);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_104);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_122);
x_123 = l_Lean_Name_mkStr4(x_2, x_3, x_109, x_122);
lean_inc(x_104);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_104);
lean_ctor_set(x_124, 1, x_122);
lean_inc(x_104);
x_125 = l_Lean_Syntax_node2(x_104, x_123, x_124, x_11);
lean_inc(x_104);
x_126 = l_Lean_Syntax_node3(x_104, x_115, x_119, x_121, x_125);
lean_inc(x_104);
x_127 = l_Lean_Syntax_node1(x_104, x_113, x_126);
lean_inc(x_104);
x_128 = l_Lean_Syntax_node1(x_104, x_111, x_127);
x_129 = l_Lean_Syntax_node2(x_104, x_106, x_108, x_128);
x_130 = lean_box(x_7);
x_131 = lean_box(x_7);
lean_inc(x_129);
x_132 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_132, 0, x_129);
lean_closure_set(x_132, 1, x_6);
lean_closure_set(x_132, 2, x_130);
lean_closure_set(x_132, 3, x_131);
x_133 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_8, x_129, x_132, x_13, x_14, x_15, x_16, x_17, x_18, x_101);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26) {
_start:
{
lean_object* x_27; lean_object* x_28; lean_object* x_38; lean_object* x_39; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_73 = lean_expr_instantiate1(x_15, x_17);
lean_inc(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_ctor_get(x_24, 5);
lean_inc(x_75);
x_76 = l_Lean_replaceRef(x_2, x_75);
lean_dec(x_75);
x_77 = lean_ctor_get(x_24, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_24, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_24, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_24, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_24, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_24, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_24, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_24, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_24, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_24, 10);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_24, sizeof(void*)*13);
x_88 = lean_ctor_get(x_24, 11);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_24, sizeof(void*)*13 + 1);
x_90 = lean_ctor_get(x_24, 12);
lean_inc(x_90);
x_91 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_78);
lean_ctor_set(x_91, 2, x_79);
lean_ctor_set(x_91, 3, x_80);
lean_ctor_set(x_91, 4, x_81);
lean_ctor_set(x_91, 5, x_76);
lean_ctor_set(x_91, 6, x_82);
lean_ctor_set(x_91, 7, x_83);
lean_ctor_set(x_91, 8, x_84);
lean_ctor_set(x_91, 9, x_85);
lean_ctor_set(x_91, 10, x_86);
lean_ctor_set(x_91, 11, x_88);
lean_ctor_set(x_91, 12, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*13, x_87);
lean_ctor_set_uint8(x_91, sizeof(void*)*13 + 1, x_89);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_74);
lean_inc(x_2);
x_92 = l_Lean_Elab_Term_elabTerm(x_2, x_74, x_3, x_3, x_20, x_21, x_22, x_23, x_91, x_25, x_26);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_box(0);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_13);
lean_inc(x_93);
x_96 = l_Lean_Elab_Term_ensureHasType(x_74, x_93, x_95, x_13, x_20, x_21, x_22, x_23, x_91, x_25, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_14);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_54 = x_97;
x_55 = x_13;
x_56 = x_98;
goto block_72;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_178; 
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
x_178 = l_Lean_Exception_isInterrupt(x_99);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = l_Lean_Exception_isRuntime(x_99);
x_101 = x_179;
goto block_177;
}
else
{
x_101 = x_178;
goto block_177;
}
block_177:
{
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_96);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_93);
x_102 = lean_infer_type(x_93, x_22, x_23, x_91, x_25, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_18);
x_105 = l_Lean_Meta_kabstract(x_103, x_18, x_14, x_22, x_23, x_91, x_25, x_104);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Expr_hasLooseBVars(x_107);
if (x_109 == 0)
{
lean_dec(x_107);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set_tag(x_105, 1);
lean_ctor_set(x_105, 0, x_99);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_free_object(x_105);
x_110 = lean_expr_instantiate1(x_107, x_17);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
x_111 = l_Lean_Meta_isExprDefEq(x_73, x_110, x_22, x_23, x_91, x_25, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
uint8_t x_114; 
lean_dec(x_107);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_111, 0);
lean_dec(x_115);
lean_ctor_set_tag(x_111, 1);
lean_ctor_set(x_111, 0, x_99);
return x_111;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_99);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_99);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_dec(x_111);
lean_inc(x_4);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
x_119 = lean_apply_9(x_4, x_18, x_107, x_20, x_21, x_22, x_23, x_91, x_25, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_120);
x_122 = l_Lean_Meta_isTypeCorrect(x_120, x_22, x_23, x_91, x_25, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_91);
lean_dec(x_13);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_120);
x_54 = x_93;
x_55 = x_126;
x_56 = x_125;
goto block_72;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_16);
x_128 = l_Lean_Meta_mkEqSymm(x_16, x_22, x_23, x_91, x_25, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
x_131 = l_Lean_Meta_mkEqRec(x_120, x_93, x_129, x_22, x_23, x_91, x_25, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_54 = x_132;
x_55 = x_13;
x_56 = x_133;
goto block_72;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_131;
}
}
else
{
lean_dec(x_120);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_128;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_120);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_122);
if (x_134 == 0)
{
return x_122;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_119;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_107);
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_111);
if (x_138 == 0)
{
return x_111;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_111, 0);
x_140 = lean_ctor_get(x_111, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_111);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_105, 0);
x_143 = lean_ctor_get(x_105, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_105);
x_144 = l_Lean_Expr_hasLooseBVars(x_142);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_142);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_99);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_expr_instantiate1(x_142, x_17);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
x_147 = l_Lean_Meta_isExprDefEq(x_73, x_146, x_22, x_23, x_91, x_25, x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_142);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
 lean_ctor_set_tag(x_152, 1);
}
lean_ctor_set(x_152, 0, x_99);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_99);
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
lean_inc(x_4);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
x_154 = lean_apply_9(x_4, x_18, x_142, x_20, x_21, x_22, x_23, x_91, x_25, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_155);
x_157 = l_Lean_Meta_isTypeCorrect(x_155, x_22, x_23, x_91, x_25, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_91);
lean_dec(x_13);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_155);
x_54 = x_93;
x_55 = x_161;
x_56 = x_160;
goto block_72;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
lean_inc(x_25);
lean_inc(x_91);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_16);
x_163 = l_Lean_Meta_mkEqSymm(x_16, x_22, x_23, x_91, x_25, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
x_166 = l_Lean_Meta_mkEqRec(x_155, x_93, x_164, x_22, x_23, x_91, x_25, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_54 = x_167;
x_55 = x_13;
x_56 = x_168;
goto block_72;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_166;
}
}
else
{
lean_dec(x_155);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_163;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_155);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_157, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_157, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_171 = x_157;
} else {
 lean_dec_ref(x_157);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_154;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_142);
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_147, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_147, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_175 = x_147;
} else {
 lean_dec_ref(x_147);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_105;
}
}
else
{
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_102;
}
}
else
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_96;
}
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_92;
}
block_37:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_1);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_mk_string_unchecked("invalid `▸` notation, failed to compute motive for the substitution", 69, 67);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_20, x_21, x_22, x_23, x_24, x_25, x_31);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor(x_1, x_16, x_27, x_20, x_21, x_22, x_23, x_24, x_25, x_35);
return x_36;
}
}
block_45:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_inc(x_18);
x_40 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate(x_17, x_18, x_22, x_23, x_24, x_25, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_isSubstCandidate(x_18, x_17, x_22, x_23, x_24, x_25, x_43);
lean_dec(x_18);
x_27 = x_39;
x_28 = x_44;
goto block_37;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
x_27 = x_39;
x_28 = x_40;
goto block_37;
}
}
block_53:
{
if (x_48 == 0)
{
if (x_3 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_51 = l_Lean_Meta_mkEqRec(x_46, x_50, x_16, x_22, x_23, x_24, x_25, x_47);
return x_51;
}
else
{
lean_dec(x_50);
lean_dec(x_46);
x_38 = x_47;
x_39 = x_49;
goto block_45;
}
}
else
{
lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_52 = l_Lean_Meta_mkEqRec(x_46, x_50, x_16, x_22, x_23, x_24, x_25, x_47);
return x_52;
}
}
block_72:
{
lean_object* x_57; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
x_57 = lean_apply_9(x_4, x_17, x_15, x_20, x_21, x_22, x_23, x_24, x_25, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_58);
x_60 = l_Lean_Meta_isTypeCorrect(x_58, x_22, x_23, x_24, x_25, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(x_3);
x_64 = lean_box(x_12);
lean_inc(x_54);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__5___boxed), 19, 11);
lean_closure_set(x_65, 0, x_54);
lean_closure_set(x_65, 1, x_5);
lean_closure_set(x_65, 2, x_6);
lean_closure_set(x_65, 3, x_7);
lean_closure_set(x_65, 4, x_8);
lean_closure_set(x_65, 5, x_9);
lean_closure_set(x_65, 6, x_63);
lean_closure_set(x_65, 7, x_10);
lean_closure_set(x_65, 8, x_11);
lean_closure_set(x_65, 9, x_64);
lean_closure_set(x_65, 10, x_2);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_66; 
x_66 = lean_unbox(x_61);
lean_dec(x_61);
x_46 = x_58;
x_47 = x_62;
x_48 = x_66;
x_49 = x_65;
x_50 = x_54;
goto block_53;
}
else
{
lean_dec(x_55);
if (x_3 == 0)
{
uint8_t x_67; 
x_67 = lean_unbox(x_61);
lean_dec(x_61);
x_46 = x_58;
x_47 = x_62;
x_48 = x_67;
x_49 = x_65;
x_50 = x_54;
goto block_53;
}
else
{
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_54);
x_38 = x_62;
x_39 = x_65;
goto block_45;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Elab_Term_tryPostponeIfHasMVars_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Term", 4, 4);
x_16 = lean_mk_string_unchecked("subst", 5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_1);
x_18 = l_Lean_Syntax_isOfKind(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_inc(x_22);
x_23 = l_Lean_Syntax_matchesNull(x_22, x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_unbox(x_25);
x_28 = lean_unbox(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_box(0);
x_34 = lean_box(x_23);
x_35 = lean_box(x_23);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_36, 0, x_32);
lean_closure_set(x_36, 1, x_33);
lean_closure_set(x_36, 2, x_34);
lean_closure_set(x_36, 3, x_35);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_36, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_41);
x_43 = lean_infer_type(x_41, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_45, x_6, x_46);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_49);
x_51 = l_Lean_Meta_matchEq_x3f(x_49, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_mk_string_unchecked("invalid `▸` notation, argument", 32, 30);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_indentExpr(x_41);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_55);
x_57 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_58);
lean_ctor_set(x_43, 0, x_47);
x_59 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_59);
lean_ctor_set(x_39, 0, x_43);
x_60 = lean_mk_string_unchecked("\nequality expected", 18, 18);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_39);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_dec(x_51);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
x_73 = lean_box(x_23);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_74, 0, x_21);
lean_closure_set(x_74, 1, x_26);
lean_closure_set(x_74, 2, x_73);
lean_closure_set(x_74, 3, x_68);
x_75 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_76; 
lean_free_object(x_47);
lean_free_object(x_43);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = l_Lean_Elab_Term_elabTerm(x_75, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_78);
x_80 = lean_infer_type(x_78, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_82);
x_85 = l_Lean_Meta_kabstract(x_82, x_71, x_84, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = l_Lean_Expr_hasLooseBVars(x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_72);
lean_inc(x_82);
x_90 = l_Lean_Meta_kabstract(x_82, x_72, x_84, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = l_Lean_Expr_hasLooseBVars(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_92);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
x_95 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = l_Lean_indentExpr(x_41);
lean_ctor_set_tag(x_90, 7);
lean_ctor_set(x_90, 1, x_97);
lean_ctor_set(x_90, 0, x_96);
x_98 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
lean_ctor_set_tag(x_85, 7);
lean_ctor_set(x_85, 1, x_99);
lean_ctor_set(x_85, 0, x_90);
x_100 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_100);
lean_ctor_set(x_80, 0, x_85);
x_101 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_102);
lean_ctor_set(x_76, 0, x_80);
x_103 = l_Lean_indentExpr(x_82);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_103);
lean_ctor_set(x_65, 0, x_76);
x_104 = lean_mk_string_unchecked("", 0, 0);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_105);
lean_ctor_set(x_64, 0, x_65);
x_106 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
return x_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_free_object(x_90);
lean_free_object(x_85);
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_111 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_93);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_92, x_112, x_72, x_71, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_113);
lean_dec(x_71);
return x_115;
}
else
{
lean_dec(x_92);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_111;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_90, 0);
x_117 = lean_ctor_get(x_90, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_90);
x_118 = l_Lean_Expr_hasLooseBVars(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_116);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
x_119 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_120 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
x_121 = l_Lean_indentExpr(x_41);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
lean_ctor_set_tag(x_85, 7);
lean_ctor_set(x_85, 1, x_124);
lean_ctor_set(x_85, 0, x_122);
x_125 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_125);
lean_ctor_set(x_80, 0, x_85);
x_126 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_127);
lean_ctor_set(x_76, 0, x_80);
x_128 = l_Lean_indentExpr(x_82);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_128);
lean_ctor_set(x_65, 0, x_76);
x_129 = lean_mk_string_unchecked("", 0, 0);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_130);
lean_ctor_set(x_64, 0, x_65);
x_131 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; 
lean_free_object(x_85);
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_box(0);
x_140 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_116, x_137, x_72, x_71, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
lean_dec(x_71);
return x_140;
}
else
{
lean_dec(x_116);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_136;
}
}
}
}
else
{
lean_free_object(x_85);
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_90;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_free_object(x_85);
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_87, x_41, x_71, x_72, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
lean_dec(x_72);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_85, 0);
x_144 = lean_ctor_get(x_85, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_85);
x_145 = l_Lean_Expr_hasLooseBVars(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_143);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_72);
lean_inc(x_82);
x_146 = l_Lean_Meta_kabstract(x_82, x_72, x_84, x_5, x_6, x_7, x_8, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = l_Lean_Expr_hasLooseBVars(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_147);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
x_151 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_152 = l_Lean_stringToMessageData(x_151);
lean_dec(x_151);
x_153 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(7, 2, 0);
} else {
 x_154 = x_149;
 lean_ctor_set_tag(x_154, 7);
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_156 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_158);
lean_ctor_set(x_80, 0, x_157);
x_159 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_160);
lean_ctor_set(x_76, 0, x_80);
x_161 = l_Lean_indentExpr(x_82);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_161);
lean_ctor_set(x_65, 0, x_76);
x_162 = lean_mk_string_unchecked("", 0, 0);
x_163 = l_Lean_stringToMessageData(x_162);
lean_dec(x_162);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_163);
lean_ctor_set(x_64, 0, x_65);
x_164 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_148);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; 
lean_dec(x_149);
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_148);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_box(0);
x_173 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_147, x_170, x_72, x_71, x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_71);
return x_173;
}
else
{
lean_dec(x_147);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_169;
}
}
}
else
{
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
x_174 = lean_box(0);
x_175 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_143, x_41, x_71, x_72, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
lean_dec(x_72);
return x_175;
}
}
}
else
{
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_85;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_80, 0);
x_177 = lean_ctor_get(x_80, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_80);
x_178 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_176);
x_179 = l_Lean_Meta_kabstract(x_176, x_71, x_178, x_5, x_6, x_7, x_8, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = l_Lean_Expr_hasLooseBVars(x_180);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_180);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_72);
lean_inc(x_176);
x_184 = l_Lean_Meta_kabstract(x_176, x_72, x_178, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Expr_hasLooseBVars(x_185);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_185);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
x_189 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
x_191 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(7, 2, 0);
} else {
 x_192 = x_187;
 lean_ctor_set_tag(x_192, 7);
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
if (lean_is_scalar(x_182)) {
 x_195 = lean_alloc_ctor(7, 2, 0);
} else {
 x_195 = x_182;
 lean_ctor_set_tag(x_195, 7);
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_indentExpr(x_49);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_199 = l_Lean_stringToMessageData(x_198);
lean_dec(x_198);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_199);
lean_ctor_set(x_76, 0, x_197);
x_200 = l_Lean_indentExpr(x_176);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_200);
lean_ctor_set(x_65, 0, x_76);
x_201 = lean_mk_string_unchecked("", 0, 0);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_202);
lean_ctor_set(x_64, 0, x_65);
x_203 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
else
{
lean_object* x_208; 
lean_dec(x_187);
lean_dec(x_182);
lean_dec(x_176);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_208 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_box(0);
x_212 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_185, x_209, x_72, x_71, x_211, x_3, x_4, x_5, x_6, x_7, x_8, x_210);
lean_dec(x_71);
return x_212;
}
else
{
lean_dec(x_185);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_208;
}
}
}
else
{
lean_dec(x_182);
lean_dec(x_176);
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_184;
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_182);
lean_dec(x_176);
lean_free_object(x_76);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
x_213 = lean_box(0);
x_214 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_78, x_180, x_41, x_71, x_72, x_213, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
lean_dec(x_72);
return x_214;
}
}
else
{
lean_dec(x_176);
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_179;
}
}
}
else
{
lean_free_object(x_76);
lean_dec(x_78);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_80;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_76, 0);
x_216 = lean_ctor_get(x_76, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_215);
x_217 = lean_infer_type(x_215, x_5, x_6, x_7, x_8, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_218);
x_222 = l_Lean_Meta_kabstract(x_218, x_71, x_221, x_5, x_6, x_7, x_8, x_219);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
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
x_226 = l_Lean_Expr_hasLooseBVars(x_223);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_223);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_72);
lean_inc(x_218);
x_227 = l_Lean_Meta_kabstract(x_218, x_72, x_221, x_5, x_6, x_7, x_8, x_224);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = l_Lean_Expr_hasLooseBVars(x_228);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_228);
lean_dec(x_215);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
x_232 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_233 = l_Lean_stringToMessageData(x_232);
lean_dec(x_232);
x_234 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_230)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_230;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_237 = l_Lean_stringToMessageData(x_236);
lean_dec(x_236);
if (lean_is_scalar(x_225)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_225;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_indentExpr(x_49);
if (lean_is_scalar(x_220)) {
 x_240 = lean_alloc_ctor(7, 2, 0);
} else {
 x_240 = x_220;
 lean_ctor_set_tag(x_240, 7);
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_242 = l_Lean_stringToMessageData(x_241);
lean_dec(x_241);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_indentExpr(x_218);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_244);
lean_ctor_set(x_65, 0, x_243);
x_245 = lean_mk_string_unchecked("", 0, 0);
x_246 = l_Lean_stringToMessageData(x_245);
lean_dec(x_245);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_246);
lean_ctor_set(x_64, 0, x_65);
x_247 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; 
lean_dec(x_230);
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_252 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_229);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_box(0);
x_256 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_215, x_228, x_253, x_72, x_71, x_255, x_3, x_4, x_5, x_6, x_7, x_8, x_254);
lean_dec(x_71);
return x_256;
}
else
{
lean_dec(x_228);
lean_dec(x_215);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_252;
}
}
}
else
{
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_227;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_65);
lean_free_object(x_64);
lean_dec(x_49);
x_257 = lean_box(0);
x_258 = l_Lean_Elab_Term_elabSubst___lam__3(x_74, x_215, x_223, x_41, x_71, x_72, x_257, x_3, x_4, x_5, x_6, x_7, x_8, x_224);
lean_dec(x_72);
return x_258;
}
}
else
{
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_222;
}
}
else
{
lean_dec(x_215);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_217;
}
}
}
else
{
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_76;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_11, 0);
lean_inc(x_259);
x_260 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_72);
lean_inc(x_259);
x_261 = l_Lean_Meta_kabstract(x_259, x_72, x_260, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_ctor_get(x_261, 1);
x_265 = l_Lean_Expr_hasLooseBVars(x_263);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_263);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_259);
x_266 = l_Lean_Meta_kabstract(x_259, x_71, x_260, x_5, x_6, x_7, x_8, x_264);
if (lean_obj_tag(x_266) == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_266, 0);
x_269 = lean_ctor_get(x_266, 1);
x_270 = l_Lean_Expr_hasLooseBVars(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_dec(x_268);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_271 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_272 = l_Lean_stringToMessageData(x_271);
lean_dec(x_271);
x_273 = l_Lean_indentExpr(x_259);
lean_ctor_set_tag(x_266, 7);
lean_ctor_set(x_266, 1, x_273);
lean_ctor_set(x_266, 0, x_272);
x_274 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_275 = l_Lean_stringToMessageData(x_274);
lean_dec(x_274);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_275);
lean_ctor_set(x_261, 0, x_266);
x_276 = l_Lean_indentExpr(x_41);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_276);
lean_ctor_set(x_65, 0, x_261);
x_277 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_278 = l_Lean_stringToMessageData(x_277);
lean_dec(x_277);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_278);
lean_ctor_set(x_64, 0, x_65);
x_279 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_279);
lean_ctor_set(x_47, 0, x_64);
x_280 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_281 = l_Lean_stringToMessageData(x_280);
lean_dec(x_280);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_281);
lean_ctor_set(x_43, 0, x_47);
x_282 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_269);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
return x_282;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_282, 0);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_282);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
else
{
lean_object* x_287; 
lean_free_object(x_266);
lean_free_object(x_261);
lean_dec(x_259);
lean_free_object(x_65);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_287 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_269);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_box(0);
x_291 = lean_unbox(x_26);
lean_inc(x_75);
x_292 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_75, x_23, x_74, x_13, x_14, x_15, x_16, x_11, x_1, x_75, x_291, x_33, x_260, x_268, x_288, x_72, x_71, x_290, x_3, x_4, x_5, x_6, x_7, x_8, x_289);
return x_292;
}
else
{
lean_dec(x_268);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_287;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_266, 0);
x_294 = lean_ctor_get(x_266, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_266);
x_295 = l_Lean_Expr_hasLooseBVars(x_293);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_293);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_296 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_297 = l_Lean_stringToMessageData(x_296);
lean_dec(x_296);
x_298 = l_Lean_indentExpr(x_259);
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_301 = l_Lean_stringToMessageData(x_300);
lean_dec(x_300);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_301);
lean_ctor_set(x_261, 0, x_299);
x_302 = l_Lean_indentExpr(x_41);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_302);
lean_ctor_set(x_65, 0, x_261);
x_303 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_304);
lean_ctor_set(x_64, 0, x_65);
x_305 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_305);
lean_ctor_set(x_47, 0, x_64);
x_306 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_307 = l_Lean_stringToMessageData(x_306);
lean_dec(x_306);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_307);
lean_ctor_set(x_43, 0, x_47);
x_308 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_294);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
else
{
lean_object* x_313; 
lean_free_object(x_261);
lean_dec(x_259);
lean_free_object(x_65);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_313 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_294);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_box(0);
x_317 = lean_unbox(x_26);
lean_inc(x_75);
x_318 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_75, x_23, x_74, x_13, x_14, x_15, x_16, x_11, x_1, x_75, x_317, x_33, x_260, x_293, x_314, x_72, x_71, x_316, x_3, x_4, x_5, x_6, x_7, x_8, x_315);
return x_318;
}
else
{
lean_dec(x_293);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_313;
}
}
}
}
else
{
lean_free_object(x_261);
lean_dec(x_259);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_266;
}
}
else
{
lean_object* x_319; uint8_t x_320; lean_object* x_321; 
lean_free_object(x_261);
lean_dec(x_259);
lean_free_object(x_65);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
x_319 = lean_box(0);
x_320 = lean_unbox(x_26);
lean_inc(x_75);
x_321 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_75, x_23, x_74, x_13, x_14, x_15, x_16, x_11, x_1, x_75, x_320, x_33, x_260, x_263, x_41, x_71, x_72, x_319, x_3, x_4, x_5, x_6, x_7, x_8, x_264);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_261, 0);
x_323 = lean_ctor_get(x_261, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_261);
x_324 = l_Lean_Expr_hasLooseBVars(x_322);
if (x_324 == 0)
{
lean_object* x_325; 
lean_dec(x_322);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_259);
x_325 = l_Lean_Meta_kabstract(x_259, x_71, x_260, x_5, x_6, x_7, x_8, x_323);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
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
x_329 = l_Lean_Expr_hasLooseBVars(x_326);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_326);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_330 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_331 = l_Lean_stringToMessageData(x_330);
lean_dec(x_330);
x_332 = l_Lean_indentExpr(x_259);
if (lean_is_scalar(x_328)) {
 x_333 = lean_alloc_ctor(7, 2, 0);
} else {
 x_333 = x_328;
 lean_ctor_set_tag(x_333, 7);
}
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_335 = l_Lean_stringToMessageData(x_334);
lean_dec(x_334);
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_335);
x_337 = l_Lean_indentExpr(x_41);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_337);
lean_ctor_set(x_65, 0, x_336);
x_338 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_339 = l_Lean_stringToMessageData(x_338);
lean_dec(x_338);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_339);
lean_ctor_set(x_64, 0, x_65);
x_340 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_340);
lean_ctor_set(x_47, 0, x_64);
x_341 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_342 = l_Lean_stringToMessageData(x_341);
lean_dec(x_341);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_342);
lean_ctor_set(x_43, 0, x_47);
x_343 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_327);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
else
{
lean_object* x_348; 
lean_dec(x_328);
lean_dec(x_259);
lean_free_object(x_65);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_348 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_327);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_box(0);
x_352 = lean_unbox(x_26);
lean_inc(x_75);
x_353 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_75, x_23, x_74, x_13, x_14, x_15, x_16, x_11, x_1, x_75, x_352, x_33, x_260, x_326, x_349, x_72, x_71, x_351, x_3, x_4, x_5, x_6, x_7, x_8, x_350);
return x_353;
}
else
{
lean_dec(x_326);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_348;
}
}
}
else
{
lean_dec(x_259);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_325;
}
}
else
{
lean_object* x_354; uint8_t x_355; lean_object* x_356; 
lean_dec(x_259);
lean_free_object(x_65);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
x_354 = lean_box(0);
x_355 = lean_unbox(x_26);
lean_inc(x_75);
x_356 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_75, x_23, x_74, x_13, x_14, x_15, x_16, x_11, x_1, x_75, x_355, x_33, x_260, x_322, x_41, x_71, x_72, x_354, x_3, x_4, x_5, x_6, x_7, x_8, x_323);
return x_356;
}
}
}
else
{
lean_dec(x_259);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_71);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_261;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_357 = lean_ctor_get(x_65, 0);
x_358 = lean_ctor_get(x_65, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_65);
x_359 = lean_box(x_23);
x_360 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_360, 0, x_21);
lean_closure_set(x_360, 1, x_26);
lean_closure_set(x_360, 2, x_359);
lean_closure_set(x_360, 3, x_68);
x_361 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_362; 
lean_free_object(x_47);
lean_free_object(x_43);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_362 = l_Lean_Elab_Term_elabTerm(x_361, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_365 = x_362;
} else {
 lean_dec_ref(x_362);
 x_365 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_363);
x_366 = lean_infer_type(x_363, x_5, x_6, x_7, x_8, x_364);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_357);
lean_inc(x_367);
x_371 = l_Lean_Meta_kabstract(x_367, x_357, x_370, x_5, x_6, x_7, x_8, x_368);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_375 = l_Lean_Expr_hasLooseBVars(x_372);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec(x_372);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_358);
lean_inc(x_367);
x_376 = l_Lean_Meta_kabstract(x_367, x_358, x_370, x_5, x_6, x_7, x_8, x_373);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
x_380 = l_Lean_Expr_hasLooseBVars(x_377);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_377);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
x_381 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_382 = l_Lean_stringToMessageData(x_381);
lean_dec(x_381);
x_383 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_379)) {
 x_384 = lean_alloc_ctor(7, 2, 0);
} else {
 x_384 = x_379;
 lean_ctor_set_tag(x_384, 7);
}
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_386 = l_Lean_stringToMessageData(x_385);
lean_dec(x_385);
if (lean_is_scalar(x_374)) {
 x_387 = lean_alloc_ctor(7, 2, 0);
} else {
 x_387 = x_374;
 lean_ctor_set_tag(x_387, 7);
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_indentExpr(x_49);
if (lean_is_scalar(x_369)) {
 x_389 = lean_alloc_ctor(7, 2, 0);
} else {
 x_389 = x_369;
 lean_ctor_set_tag(x_389, 7);
}
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_391 = l_Lean_stringToMessageData(x_390);
lean_dec(x_390);
if (lean_is_scalar(x_365)) {
 x_392 = lean_alloc_ctor(7, 2, 0);
} else {
 x_392 = x_365;
 lean_ctor_set_tag(x_392, 7);
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_indentExpr(x_367);
x_394 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_mk_string_unchecked("", 0, 0);
x_396 = l_Lean_stringToMessageData(x_395);
lean_dec(x_395);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_396);
lean_ctor_set(x_64, 0, x_394);
x_397 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_378);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
else
{
lean_object* x_402; 
lean_dec(x_379);
lean_dec(x_374);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_365);
lean_free_object(x_64);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_402 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_378);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_box(0);
x_406 = l_Lean_Elab_Term_elabSubst___lam__3(x_360, x_363, x_377, x_403, x_358, x_357, x_405, x_3, x_4, x_5, x_6, x_7, x_8, x_404);
lean_dec(x_357);
return x_406;
}
else
{
lean_dec(x_377);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_402;
}
}
}
else
{
lean_dec(x_374);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_376;
}
}
else
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_374);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_365);
lean_free_object(x_64);
lean_dec(x_49);
x_407 = lean_box(0);
x_408 = l_Lean_Elab_Term_elabSubst___lam__3(x_360, x_363, x_372, x_41, x_357, x_358, x_407, x_3, x_4, x_5, x_6, x_7, x_8, x_373);
lean_dec(x_358);
return x_408;
}
}
else
{
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_371;
}
}
else
{
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_366;
}
}
else
{
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_362;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_11, 0);
lean_inc(x_409);
x_410 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_358);
lean_inc(x_409);
x_411 = l_Lean_Meta_kabstract(x_409, x_358, x_410, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
x_415 = l_Lean_Expr_hasLooseBVars(x_412);
if (x_415 == 0)
{
lean_object* x_416; 
lean_dec(x_412);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_357);
lean_inc(x_409);
x_416 = l_Lean_Meta_kabstract(x_409, x_357, x_410, x_5, x_6, x_7, x_8, x_413);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = l_Lean_Expr_hasLooseBVars(x_417);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_417);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_421 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_422 = l_Lean_stringToMessageData(x_421);
lean_dec(x_421);
x_423 = l_Lean_indentExpr(x_409);
if (lean_is_scalar(x_419)) {
 x_424 = lean_alloc_ctor(7, 2, 0);
} else {
 x_424 = x_419;
 lean_ctor_set_tag(x_424, 7);
}
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_426 = l_Lean_stringToMessageData(x_425);
lean_dec(x_425);
if (lean_is_scalar(x_414)) {
 x_427 = lean_alloc_ctor(7, 2, 0);
} else {
 x_427 = x_414;
 lean_ctor_set_tag(x_427, 7);
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_426);
x_428 = l_Lean_indentExpr(x_41);
x_429 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_431 = l_Lean_stringToMessageData(x_430);
lean_dec(x_430);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_431);
lean_ctor_set(x_64, 0, x_429);
x_432 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_432);
lean_ctor_set(x_47, 0, x_64);
x_433 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_434 = l_Lean_stringToMessageData(x_433);
lean_dec(x_433);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_434);
lean_ctor_set(x_43, 0, x_47);
x_435 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_418);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
else
{
lean_object* x_440; 
lean_dec(x_419);
lean_dec(x_414);
lean_dec(x_409);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_440 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_418);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_box(0);
x_444 = lean_unbox(x_26);
lean_inc(x_361);
x_445 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_361, x_23, x_360, x_13, x_14, x_15, x_16, x_11, x_1, x_361, x_444, x_33, x_410, x_417, x_441, x_358, x_357, x_443, x_3, x_4, x_5, x_6, x_7, x_8, x_442);
return x_445;
}
else
{
lean_dec(x_417);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_440;
}
}
}
else
{
lean_dec(x_414);
lean_dec(x_409);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_416;
}
}
else
{
lean_object* x_446; uint8_t x_447; lean_object* x_448; 
lean_dec(x_414);
lean_dec(x_409);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
x_446 = lean_box(0);
x_447 = lean_unbox(x_26);
lean_inc(x_361);
x_448 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_361, x_23, x_360, x_13, x_14, x_15, x_16, x_11, x_1, x_361, x_447, x_33, x_410, x_412, x_41, x_357, x_358, x_446, x_3, x_4, x_5, x_6, x_7, x_8, x_413);
return x_448;
}
}
else
{
lean_dec(x_409);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_357);
lean_free_object(x_64);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_411;
}
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_449 = lean_ctor_get(x_64, 0);
lean_inc(x_449);
lean_dec(x_64);
x_450 = lean_ctor_get(x_65, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_65, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_452 = x_65;
} else {
 lean_dec_ref(x_65);
 x_452 = lean_box(0);
}
x_453 = lean_box(x_23);
x_454 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_454, 0, x_21);
lean_closure_set(x_454, 1, x_26);
lean_closure_set(x_454, 2, x_453);
lean_closure_set(x_454, 3, x_449);
x_455 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_456; 
lean_free_object(x_47);
lean_free_object(x_43);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_456 = l_Lean_Elab_Term_elabTerm(x_455, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_459 = x_456;
} else {
 lean_dec_ref(x_456);
 x_459 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_457);
x_460 = lean_infer_type(x_457, x_5, x_6, x_7, x_8, x_458);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_463 = x_460;
} else {
 lean_dec_ref(x_460);
 x_463 = lean_box(0);
}
x_464 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_450);
lean_inc(x_461);
x_465 = l_Lean_Meta_kabstract(x_461, x_450, x_464, x_5, x_6, x_7, x_8, x_462);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
x_469 = l_Lean_Expr_hasLooseBVars(x_466);
if (x_469 == 0)
{
lean_object* x_470; 
lean_dec(x_466);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_451);
lean_inc(x_461);
x_470 = l_Lean_Meta_kabstract(x_461, x_451, x_464, x_5, x_6, x_7, x_8, x_467);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
x_474 = l_Lean_Expr_hasLooseBVars(x_471);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_471);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_451);
lean_dec(x_450);
x_475 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_476 = l_Lean_stringToMessageData(x_475);
lean_dec(x_475);
x_477 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_473)) {
 x_478 = lean_alloc_ctor(7, 2, 0);
} else {
 x_478 = x_473;
 lean_ctor_set_tag(x_478, 7);
}
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_480 = l_Lean_stringToMessageData(x_479);
lean_dec(x_479);
if (lean_is_scalar(x_468)) {
 x_481 = lean_alloc_ctor(7, 2, 0);
} else {
 x_481 = x_468;
 lean_ctor_set_tag(x_481, 7);
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_480);
x_482 = l_Lean_indentExpr(x_49);
if (lean_is_scalar(x_463)) {
 x_483 = lean_alloc_ctor(7, 2, 0);
} else {
 x_483 = x_463;
 lean_ctor_set_tag(x_483, 7);
}
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_485 = l_Lean_stringToMessageData(x_484);
lean_dec(x_484);
if (lean_is_scalar(x_459)) {
 x_486 = lean_alloc_ctor(7, 2, 0);
} else {
 x_486 = x_459;
 lean_ctor_set_tag(x_486, 7);
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_485);
x_487 = l_Lean_indentExpr(x_461);
if (lean_is_scalar(x_452)) {
 x_488 = lean_alloc_ctor(7, 2, 0);
} else {
 x_488 = x_452;
 lean_ctor_set_tag(x_488, 7);
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_mk_string_unchecked("", 0, 0);
x_490 = l_Lean_stringToMessageData(x_489);
lean_dec(x_489);
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_491, x_3, x_4, x_5, x_6, x_7, x_8, x_472);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
else
{
lean_object* x_497; 
lean_dec(x_473);
lean_dec(x_468);
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_497 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_472);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_box(0);
x_501 = l_Lean_Elab_Term_elabSubst___lam__3(x_454, x_457, x_471, x_498, x_451, x_450, x_500, x_3, x_4, x_5, x_6, x_7, x_8, x_499);
lean_dec(x_450);
return x_501;
}
else
{
lean_dec(x_471);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_497;
}
}
}
else
{
lean_dec(x_468);
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_470;
}
}
else
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_468);
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_452);
lean_dec(x_49);
x_502 = lean_box(0);
x_503 = l_Lean_Elab_Term_elabSubst___lam__3(x_454, x_457, x_466, x_41, x_450, x_451, x_502, x_3, x_4, x_5, x_6, x_7, x_8, x_467);
lean_dec(x_451);
return x_503;
}
}
else
{
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_465;
}
}
else
{
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_460;
}
}
else
{
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_456;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_11, 0);
lean_inc(x_504);
x_505 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_451);
lean_inc(x_504);
x_506 = l_Lean_Meta_kabstract(x_504, x_451, x_505, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_509 = x_506;
} else {
 lean_dec_ref(x_506);
 x_509 = lean_box(0);
}
x_510 = l_Lean_Expr_hasLooseBVars(x_507);
if (x_510 == 0)
{
lean_object* x_511; 
lean_dec(x_507);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_450);
lean_inc(x_504);
x_511 = l_Lean_Meta_kabstract(x_504, x_450, x_505, x_5, x_6, x_7, x_8, x_508);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
x_515 = l_Lean_Expr_hasLooseBVars(x_512);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_512);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_516 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_517 = l_Lean_stringToMessageData(x_516);
lean_dec(x_516);
x_518 = l_Lean_indentExpr(x_504);
if (lean_is_scalar(x_514)) {
 x_519 = lean_alloc_ctor(7, 2, 0);
} else {
 x_519 = x_514;
 lean_ctor_set_tag(x_519, 7);
}
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_521 = l_Lean_stringToMessageData(x_520);
lean_dec(x_520);
if (lean_is_scalar(x_509)) {
 x_522 = lean_alloc_ctor(7, 2, 0);
} else {
 x_522 = x_509;
 lean_ctor_set_tag(x_522, 7);
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_521);
x_523 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_452)) {
 x_524 = lean_alloc_ctor(7, 2, 0);
} else {
 x_524 = x_452;
 lean_ctor_set_tag(x_524, 7);
}
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_526 = l_Lean_stringToMessageData(x_525);
lean_dec(x_525);
x_527 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_indentExpr(x_49);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_528);
lean_ctor_set(x_47, 0, x_527);
x_529 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_530 = l_Lean_stringToMessageData(x_529);
lean_dec(x_529);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_530);
lean_ctor_set(x_43, 0, x_47);
x_531 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_513);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_534 = x_531;
} else {
 lean_dec_ref(x_531);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
else
{
lean_object* x_536; 
lean_dec(x_514);
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_452);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_536 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_513);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_box(0);
x_540 = lean_unbox(x_26);
lean_inc(x_455);
x_541 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_455, x_23, x_454, x_13, x_14, x_15, x_16, x_11, x_1, x_455, x_540, x_33, x_505, x_512, x_537, x_451, x_450, x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_538);
return x_541;
}
else
{
lean_dec(x_512);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_536;
}
}
}
else
{
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_511;
}
}
else
{
lean_object* x_542; uint8_t x_543; lean_object* x_544; 
lean_dec(x_509);
lean_dec(x_504);
lean_dec(x_452);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
x_542 = lean_box(0);
x_543 = lean_unbox(x_26);
lean_inc(x_455);
x_544 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_455, x_23, x_454, x_13, x_14, x_15, x_16, x_11, x_1, x_455, x_543, x_33, x_505, x_507, x_41, x_450, x_451, x_542, x_3, x_4, x_5, x_6, x_7, x_8, x_508);
return x_544;
}
}
else
{
lean_dec(x_504);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_506;
}
}
}
}
}
else
{
uint8_t x_545; 
lean_free_object(x_47);
lean_dec(x_49);
lean_free_object(x_43);
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_545 = !lean_is_exclusive(x_51);
if (x_545 == 0)
{
return x_51;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_51, 0);
x_547 = lean_ctor_get(x_51, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_51);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_47, 0);
x_550 = lean_ctor_get(x_47, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_549);
x_551 = l_Lean_Meta_matchEq_x3f(x_549, x_5, x_6, x_7, x_8, x_550);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_mk_string_unchecked("invalid `▸` notation, argument", 32, 30);
x_555 = l_Lean_stringToMessageData(x_554);
lean_dec(x_554);
x_556 = l_Lean_indentExpr(x_41);
x_557 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_559 = l_Lean_stringToMessageData(x_558);
lean_dec(x_558);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_559);
lean_ctor_set(x_43, 0, x_557);
x_560 = l_Lean_indentExpr(x_549);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_560);
lean_ctor_set(x_39, 0, x_43);
x_561 = lean_mk_string_unchecked("\nequality expected", 18, 18);
x_562 = l_Lean_stringToMessageData(x_561);
lean_dec(x_561);
x_563 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_563, 0, x_39);
lean_ctor_set(x_563, 1, x_562);
x_564 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_563, x_3, x_4, x_5, x_6, x_7, x_8, x_553);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_564;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_free_object(x_39);
x_565 = lean_ctor_get(x_552, 0);
lean_inc(x_565);
lean_dec(x_552);
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
x_567 = lean_ctor_get(x_551, 1);
lean_inc(x_567);
lean_dec(x_551);
x_568 = lean_ctor_get(x_565, 0);
lean_inc(x_568);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_569 = x_565;
} else {
 lean_dec_ref(x_565);
 x_569 = lean_box(0);
}
x_570 = lean_ctor_get(x_566, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_566, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_572 = x_566;
} else {
 lean_dec_ref(x_566);
 x_572 = lean_box(0);
}
x_573 = lean_box(x_23);
x_574 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_574, 0, x_21);
lean_closure_set(x_574, 1, x_26);
lean_closure_set(x_574, 2, x_573);
lean_closure_set(x_574, 3, x_568);
x_575 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_576; 
lean_free_object(x_43);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_576 = l_Lean_Elab_Term_elabTerm(x_575, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_577);
x_580 = lean_infer_type(x_577, x_5, x_6, x_7, x_8, x_578);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_583 = x_580;
} else {
 lean_dec_ref(x_580);
 x_583 = lean_box(0);
}
x_584 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_570);
lean_inc(x_581);
x_585 = l_Lean_Meta_kabstract(x_581, x_570, x_584, x_5, x_6, x_7, x_8, x_582);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
x_589 = l_Lean_Expr_hasLooseBVars(x_586);
if (x_589 == 0)
{
lean_object* x_590; 
lean_dec(x_586);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_571);
lean_inc(x_581);
x_590 = l_Lean_Meta_kabstract(x_581, x_571, x_584, x_5, x_6, x_7, x_8, x_587);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_593 = x_590;
} else {
 lean_dec_ref(x_590);
 x_593 = lean_box(0);
}
x_594 = l_Lean_Expr_hasLooseBVars(x_591);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_591);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
x_595 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_596 = l_Lean_stringToMessageData(x_595);
lean_dec(x_595);
x_597 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_593)) {
 x_598 = lean_alloc_ctor(7, 2, 0);
} else {
 x_598 = x_593;
 lean_ctor_set_tag(x_598, 7);
}
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_600 = l_Lean_stringToMessageData(x_599);
lean_dec(x_599);
if (lean_is_scalar(x_588)) {
 x_601 = lean_alloc_ctor(7, 2, 0);
} else {
 x_601 = x_588;
 lean_ctor_set_tag(x_601, 7);
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_600);
x_602 = l_Lean_indentExpr(x_549);
if (lean_is_scalar(x_583)) {
 x_603 = lean_alloc_ctor(7, 2, 0);
} else {
 x_603 = x_583;
 lean_ctor_set_tag(x_603, 7);
}
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_605 = l_Lean_stringToMessageData(x_604);
lean_dec(x_604);
if (lean_is_scalar(x_579)) {
 x_606 = lean_alloc_ctor(7, 2, 0);
} else {
 x_606 = x_579;
 lean_ctor_set_tag(x_606, 7);
}
lean_ctor_set(x_606, 0, x_603);
lean_ctor_set(x_606, 1, x_605);
x_607 = l_Lean_indentExpr(x_581);
if (lean_is_scalar(x_572)) {
 x_608 = lean_alloc_ctor(7, 2, 0);
} else {
 x_608 = x_572;
 lean_ctor_set_tag(x_608, 7);
}
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_mk_string_unchecked("", 0, 0);
x_610 = l_Lean_stringToMessageData(x_609);
lean_dec(x_609);
if (lean_is_scalar(x_569)) {
 x_611 = lean_alloc_ctor(7, 2, 0);
} else {
 x_611 = x_569;
 lean_ctor_set_tag(x_611, 7);
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_610);
x_612 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_611, x_3, x_4, x_5, x_6, x_7, x_8, x_592);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_615 = x_612;
} else {
 lean_dec_ref(x_612);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
else
{
lean_object* x_617; 
lean_dec(x_593);
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_549);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_617 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_592);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_box(0);
x_621 = l_Lean_Elab_Term_elabSubst___lam__3(x_574, x_577, x_591, x_618, x_571, x_570, x_620, x_3, x_4, x_5, x_6, x_7, x_8, x_619);
lean_dec(x_570);
return x_621;
}
else
{
lean_dec(x_591);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_617;
}
}
}
else
{
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_590;
}
}
else
{
lean_object* x_622; lean_object* x_623; 
lean_dec(x_588);
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_549);
x_622 = lean_box(0);
x_623 = l_Lean_Elab_Term_elabSubst___lam__3(x_574, x_577, x_586, x_41, x_570, x_571, x_622, x_3, x_4, x_5, x_6, x_7, x_8, x_587);
lean_dec(x_571);
return x_623;
}
}
else
{
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_585;
}
}
else
{
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_580;
}
}
else
{
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_576;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_11, 0);
lean_inc(x_624);
x_625 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_571);
lean_inc(x_624);
x_626 = l_Lean_Meta_kabstract(x_624, x_571, x_625, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
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
x_630 = l_Lean_Expr_hasLooseBVars(x_627);
if (x_630 == 0)
{
lean_object* x_631; 
lean_dec(x_627);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_570);
lean_inc(x_624);
x_631 = l_Lean_Meta_kabstract(x_624, x_570, x_625, x_5, x_6, x_7, x_8, x_628);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_635 = l_Lean_Expr_hasLooseBVars(x_632);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_632);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_636 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_637 = l_Lean_stringToMessageData(x_636);
lean_dec(x_636);
x_638 = l_Lean_indentExpr(x_624);
if (lean_is_scalar(x_634)) {
 x_639 = lean_alloc_ctor(7, 2, 0);
} else {
 x_639 = x_634;
 lean_ctor_set_tag(x_639, 7);
}
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_641 = l_Lean_stringToMessageData(x_640);
lean_dec(x_640);
if (lean_is_scalar(x_629)) {
 x_642 = lean_alloc_ctor(7, 2, 0);
} else {
 x_642 = x_629;
 lean_ctor_set_tag(x_642, 7);
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_641);
x_643 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_572)) {
 x_644 = lean_alloc_ctor(7, 2, 0);
} else {
 x_644 = x_572;
 lean_ctor_set_tag(x_644, 7);
}
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
x_645 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_646 = l_Lean_stringToMessageData(x_645);
lean_dec(x_645);
if (lean_is_scalar(x_569)) {
 x_647 = lean_alloc_ctor(7, 2, 0);
} else {
 x_647 = x_569;
 lean_ctor_set_tag(x_647, 7);
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_indentExpr(x_549);
x_649 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_651 = l_Lean_stringToMessageData(x_650);
lean_dec(x_650);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_651);
lean_ctor_set(x_43, 0, x_649);
x_652 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_633);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_655 = x_652;
} else {
 lean_dec_ref(x_652);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
else
{
lean_object* x_657; 
lean_dec(x_634);
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_549);
lean_free_object(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_657 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_633);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; lean_object* x_662; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_box(0);
x_661 = lean_unbox(x_26);
lean_inc(x_575);
x_662 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_575, x_23, x_574, x_13, x_14, x_15, x_16, x_11, x_1, x_575, x_661, x_33, x_625, x_632, x_658, x_571, x_570, x_660, x_3, x_4, x_5, x_6, x_7, x_8, x_659);
return x_662;
}
else
{
lean_dec(x_632);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_657;
}
}
}
else
{
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_631;
}
}
else
{
lean_object* x_663; uint8_t x_664; lean_object* x_665; 
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_549);
lean_free_object(x_43);
x_663 = lean_box(0);
x_664 = lean_unbox(x_26);
lean_inc(x_575);
x_665 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_575, x_23, x_574, x_13, x_14, x_15, x_16, x_11, x_1, x_575, x_664, x_33, x_625, x_627, x_41, x_570, x_571, x_663, x_3, x_4, x_5, x_6, x_7, x_8, x_628);
return x_665;
}
}
else
{
lean_dec(x_624);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_549);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_626;
}
}
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_549);
lean_free_object(x_43);
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_666 = lean_ctor_get(x_551, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_551, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_668 = x_551;
} else {
 lean_dec_ref(x_551);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_670 = lean_ctor_get(x_43, 0);
x_671 = lean_ctor_get(x_43, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_43);
x_672 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_670, x_6, x_671);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_673);
x_676 = l_Lean_Meta_matchEq_x3f(x_673, x_5, x_6, x_7, x_8, x_674);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = lean_mk_string_unchecked("invalid `▸` notation, argument", 32, 30);
x_680 = l_Lean_stringToMessageData(x_679);
lean_dec(x_679);
x_681 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_675)) {
 x_682 = lean_alloc_ctor(7, 2, 0);
} else {
 x_682 = x_675;
 lean_ctor_set_tag(x_682, 7);
}
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set(x_682, 1, x_681);
x_683 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_684 = l_Lean_stringToMessageData(x_683);
lean_dec(x_683);
x_685 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_685, 0, x_682);
lean_ctor_set(x_685, 1, x_684);
x_686 = l_Lean_indentExpr(x_673);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_686);
lean_ctor_set(x_39, 0, x_685);
x_687 = lean_mk_string_unchecked("\nequality expected", 18, 18);
x_688 = l_Lean_stringToMessageData(x_687);
lean_dec(x_687);
x_689 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_689, 0, x_39);
lean_ctor_set(x_689, 1, x_688);
x_690 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_689, x_3, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_690;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_free_object(x_39);
x_691 = lean_ctor_get(x_677, 0);
lean_inc(x_691);
lean_dec(x_677);
x_692 = lean_ctor_get(x_691, 1);
lean_inc(x_692);
x_693 = lean_ctor_get(x_676, 1);
lean_inc(x_693);
lean_dec(x_676);
x_694 = lean_ctor_get(x_691, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_695 = x_691;
} else {
 lean_dec_ref(x_691);
 x_695 = lean_box(0);
}
x_696 = lean_ctor_get(x_692, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_692, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 lean_ctor_release(x_692, 1);
 x_698 = x_692;
} else {
 lean_dec_ref(x_692);
 x_698 = lean_box(0);
}
x_699 = lean_box(x_23);
x_700 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_700, 0, x_21);
lean_closure_set(x_700, 1, x_26);
lean_closure_set(x_700, 2, x_699);
lean_closure_set(x_700, 3, x_694);
x_701 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_702; 
lean_dec(x_675);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_702 = l_Lean_Elab_Term_elabTerm(x_701, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_693);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_705 = x_702;
} else {
 lean_dec_ref(x_702);
 x_705 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_703);
x_706 = lean_infer_type(x_703, x_5, x_6, x_7, x_8, x_704);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_709 = x_706;
} else {
 lean_dec_ref(x_706);
 x_709 = lean_box(0);
}
x_710 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_696);
lean_inc(x_707);
x_711 = l_Lean_Meta_kabstract(x_707, x_696, x_710, x_5, x_6, x_7, x_8, x_708);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_714 = x_711;
} else {
 lean_dec_ref(x_711);
 x_714 = lean_box(0);
}
x_715 = l_Lean_Expr_hasLooseBVars(x_712);
if (x_715 == 0)
{
lean_object* x_716; 
lean_dec(x_712);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_697);
lean_inc(x_707);
x_716 = l_Lean_Meta_kabstract(x_707, x_697, x_710, x_5, x_6, x_7, x_8, x_713);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_719 = x_716;
} else {
 lean_dec_ref(x_716);
 x_719 = lean_box(0);
}
x_720 = l_Lean_Expr_hasLooseBVars(x_717);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_717);
lean_dec(x_703);
lean_dec(x_700);
lean_dec(x_697);
lean_dec(x_696);
x_721 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_722 = l_Lean_stringToMessageData(x_721);
lean_dec(x_721);
x_723 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_719)) {
 x_724 = lean_alloc_ctor(7, 2, 0);
} else {
 x_724 = x_719;
 lean_ctor_set_tag(x_724, 7);
}
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
x_725 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_726 = l_Lean_stringToMessageData(x_725);
lean_dec(x_725);
if (lean_is_scalar(x_714)) {
 x_727 = lean_alloc_ctor(7, 2, 0);
} else {
 x_727 = x_714;
 lean_ctor_set_tag(x_727, 7);
}
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_726);
x_728 = l_Lean_indentExpr(x_673);
if (lean_is_scalar(x_709)) {
 x_729 = lean_alloc_ctor(7, 2, 0);
} else {
 x_729 = x_709;
 lean_ctor_set_tag(x_729, 7);
}
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_731 = l_Lean_stringToMessageData(x_730);
lean_dec(x_730);
if (lean_is_scalar(x_705)) {
 x_732 = lean_alloc_ctor(7, 2, 0);
} else {
 x_732 = x_705;
 lean_ctor_set_tag(x_732, 7);
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_731);
x_733 = l_Lean_indentExpr(x_707);
if (lean_is_scalar(x_698)) {
 x_734 = lean_alloc_ctor(7, 2, 0);
} else {
 x_734 = x_698;
 lean_ctor_set_tag(x_734, 7);
}
lean_ctor_set(x_734, 0, x_732);
lean_ctor_set(x_734, 1, x_733);
x_735 = lean_mk_string_unchecked("", 0, 0);
x_736 = l_Lean_stringToMessageData(x_735);
lean_dec(x_735);
if (lean_is_scalar(x_695)) {
 x_737 = lean_alloc_ctor(7, 2, 0);
} else {
 x_737 = x_695;
 lean_ctor_set_tag(x_737, 7);
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_736);
x_738 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_737, x_3, x_4, x_5, x_6, x_7, x_8, x_718);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_741 = x_738;
} else {
 lean_dec_ref(x_738);
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
else
{
lean_object* x_743; 
lean_dec(x_719);
lean_dec(x_714);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_698);
lean_dec(x_695);
lean_dec(x_673);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_743 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_718);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_box(0);
x_747 = l_Lean_Elab_Term_elabSubst___lam__3(x_700, x_703, x_717, x_744, x_697, x_696, x_746, x_3, x_4, x_5, x_6, x_7, x_8, x_745);
lean_dec(x_696);
return x_747;
}
else
{
lean_dec(x_717);
lean_dec(x_703);
lean_dec(x_700);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_743;
}
}
}
else
{
lean_dec(x_714);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_703);
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_716;
}
}
else
{
lean_object* x_748; lean_object* x_749; 
lean_dec(x_714);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_698);
lean_dec(x_695);
lean_dec(x_673);
x_748 = lean_box(0);
x_749 = l_Lean_Elab_Term_elabSubst___lam__3(x_700, x_703, x_712, x_41, x_696, x_697, x_748, x_3, x_4, x_5, x_6, x_7, x_8, x_713);
lean_dec(x_697);
return x_749;
}
}
else
{
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_703);
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_711;
}
}
else
{
lean_dec(x_705);
lean_dec(x_703);
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_706;
}
}
else
{
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_702;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_11, 0);
lean_inc(x_750);
x_751 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_697);
lean_inc(x_750);
x_752 = l_Lean_Meta_kabstract(x_750, x_697, x_751, x_5, x_6, x_7, x_8, x_693);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_755 = x_752;
} else {
 lean_dec_ref(x_752);
 x_755 = lean_box(0);
}
x_756 = l_Lean_Expr_hasLooseBVars(x_753);
if (x_756 == 0)
{
lean_object* x_757; 
lean_dec(x_753);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_696);
lean_inc(x_750);
x_757 = l_Lean_Meta_kabstract(x_750, x_696, x_751, x_5, x_6, x_7, x_8, x_754);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_760 = x_757;
} else {
 lean_dec_ref(x_757);
 x_760 = lean_box(0);
}
x_761 = l_Lean_Expr_hasLooseBVars(x_758);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_758);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_762 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_763 = l_Lean_stringToMessageData(x_762);
lean_dec(x_762);
x_764 = l_Lean_indentExpr(x_750);
if (lean_is_scalar(x_760)) {
 x_765 = lean_alloc_ctor(7, 2, 0);
} else {
 x_765 = x_760;
 lean_ctor_set_tag(x_765, 7);
}
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
x_766 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_767 = l_Lean_stringToMessageData(x_766);
lean_dec(x_766);
if (lean_is_scalar(x_755)) {
 x_768 = lean_alloc_ctor(7, 2, 0);
} else {
 x_768 = x_755;
 lean_ctor_set_tag(x_768, 7);
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_767);
x_769 = l_Lean_indentExpr(x_41);
if (lean_is_scalar(x_698)) {
 x_770 = lean_alloc_ctor(7, 2, 0);
} else {
 x_770 = x_698;
 lean_ctor_set_tag(x_770, 7);
}
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
x_771 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_772 = l_Lean_stringToMessageData(x_771);
lean_dec(x_771);
if (lean_is_scalar(x_695)) {
 x_773 = lean_alloc_ctor(7, 2, 0);
} else {
 x_773 = x_695;
 lean_ctor_set_tag(x_773, 7);
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_772);
x_774 = l_Lean_indentExpr(x_673);
if (lean_is_scalar(x_675)) {
 x_775 = lean_alloc_ctor(7, 2, 0);
} else {
 x_775 = x_675;
 lean_ctor_set_tag(x_775, 7);
}
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
x_776 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_777 = l_Lean_stringToMessageData(x_776);
lean_dec(x_776);
x_778 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_777);
x_779 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_778, x_3, x_4, x_5, x_6, x_7, x_8, x_759);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_782 = x_779;
} else {
 lean_dec_ref(x_779);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_781);
return x_783;
}
else
{
lean_object* x_784; 
lean_dec(x_760);
lean_dec(x_755);
lean_dec(x_750);
lean_dec(x_698);
lean_dec(x_695);
lean_dec(x_675);
lean_dec(x_673);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_784 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_759);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = lean_box(0);
x_788 = lean_unbox(x_26);
lean_inc(x_701);
x_789 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_701, x_23, x_700, x_13, x_14, x_15, x_16, x_11, x_1, x_701, x_788, x_33, x_751, x_758, x_785, x_697, x_696, x_787, x_3, x_4, x_5, x_6, x_7, x_8, x_786);
return x_789;
}
else
{
lean_dec(x_758);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_784;
}
}
}
else
{
lean_dec(x_755);
lean_dec(x_750);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_757;
}
}
else
{
lean_object* x_790; uint8_t x_791; lean_object* x_792; 
lean_dec(x_755);
lean_dec(x_750);
lean_dec(x_698);
lean_dec(x_695);
lean_dec(x_675);
lean_dec(x_673);
x_790 = lean_box(0);
x_791 = lean_unbox(x_26);
lean_inc(x_701);
x_792 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_701, x_23, x_700, x_13, x_14, x_15, x_16, x_11, x_1, x_701, x_791, x_33, x_751, x_753, x_41, x_696, x_697, x_790, x_3, x_4, x_5, x_6, x_7, x_8, x_754);
return x_792;
}
}
else
{
lean_dec(x_750);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_752;
}
}
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_675);
lean_dec(x_673);
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_793 = lean_ctor_get(x_676, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_676, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_795 = x_676;
} else {
 lean_dec_ref(x_676);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
}
}
else
{
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_43;
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_39, 0);
x_798 = lean_ctor_get(x_39, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_797);
x_799 = lean_infer_type(x_797, x_5, x_6, x_7, x_8, x_798);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
x_803 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_800, x_6, x_801);
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_804);
x_807 = l_Lean_Meta_matchEq_x3f(x_804, x_5, x_6, x_7, x_8, x_805);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_mk_string_unchecked("invalid `▸` notation, argument", 32, 30);
x_811 = l_Lean_stringToMessageData(x_810);
lean_dec(x_810);
x_812 = l_Lean_indentExpr(x_797);
if (lean_is_scalar(x_806)) {
 x_813 = lean_alloc_ctor(7, 2, 0);
} else {
 x_813 = x_806;
 lean_ctor_set_tag(x_813, 7);
}
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set(x_813, 1, x_812);
x_814 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_815 = l_Lean_stringToMessageData(x_814);
lean_dec(x_814);
if (lean_is_scalar(x_802)) {
 x_816 = lean_alloc_ctor(7, 2, 0);
} else {
 x_816 = x_802;
 lean_ctor_set_tag(x_816, 7);
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_815);
x_817 = l_Lean_indentExpr(x_804);
x_818 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
x_819 = lean_mk_string_unchecked("\nequality expected", 18, 18);
x_820 = l_Lean_stringToMessageData(x_819);
lean_dec(x_819);
x_821 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_821, 0, x_818);
lean_ctor_set(x_821, 1, x_820);
x_822 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_821, x_3, x_4, x_5, x_6, x_7, x_8, x_809);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_822;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_823 = lean_ctor_get(x_808, 0);
lean_inc(x_823);
lean_dec(x_808);
x_824 = lean_ctor_get(x_823, 1);
lean_inc(x_824);
x_825 = lean_ctor_get(x_807, 1);
lean_inc(x_825);
lean_dec(x_807);
x_826 = lean_ctor_get(x_823, 0);
lean_inc(x_826);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_827 = x_823;
} else {
 lean_dec_ref(x_823);
 x_827 = lean_box(0);
}
x_828 = lean_ctor_get(x_824, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_824, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_830 = x_824;
} else {
 lean_dec_ref(x_824);
 x_830 = lean_box(0);
}
x_831 = lean_box(x_23);
x_832 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lam__2___boxed), 13, 4);
lean_closure_set(x_832, 0, x_21);
lean_closure_set(x_832, 1, x_26);
lean_closure_set(x_832, 2, x_831);
lean_closure_set(x_832, 3, x_826);
x_833 = l_Lean_Syntax_getArg(x_22, x_31);
lean_dec(x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_834; 
lean_dec(x_806);
lean_dec(x_802);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_834 = l_Lean_Elab_Term_elabTerm(x_833, x_33, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_825);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 x_837 = x_834;
} else {
 lean_dec_ref(x_834);
 x_837 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_835);
x_838 = lean_infer_type(x_835, x_5, x_6, x_7, x_8, x_836);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_841 = x_838;
} else {
 lean_dec_ref(x_838);
 x_841 = lean_box(0);
}
x_842 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_828);
lean_inc(x_839);
x_843 = l_Lean_Meta_kabstract(x_839, x_828, x_842, x_5, x_6, x_7, x_8, x_840);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; uint8_t x_847; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_846 = x_843;
} else {
 lean_dec_ref(x_843);
 x_846 = lean_box(0);
}
x_847 = l_Lean_Expr_hasLooseBVars(x_844);
if (x_847 == 0)
{
lean_object* x_848; 
lean_dec(x_844);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_829);
lean_inc(x_839);
x_848 = l_Lean_Meta_kabstract(x_839, x_829, x_842, x_5, x_6, x_7, x_8, x_845);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 x_851 = x_848;
} else {
 lean_dec_ref(x_848);
 x_851 = lean_box(0);
}
x_852 = l_Lean_Expr_hasLooseBVars(x_849);
if (x_852 == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_849);
lean_dec(x_835);
lean_dec(x_832);
lean_dec(x_829);
lean_dec(x_828);
x_853 = lean_mk_string_unchecked("invalid `▸` notation, the equality", 36, 34);
x_854 = l_Lean_stringToMessageData(x_853);
lean_dec(x_853);
x_855 = l_Lean_indentExpr(x_797);
if (lean_is_scalar(x_851)) {
 x_856 = lean_alloc_ctor(7, 2, 0);
} else {
 x_856 = x_851;
 lean_ctor_set_tag(x_856, 7);
}
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
x_857 = lean_mk_string_unchecked("\nhas type ", 10, 10);
x_858 = l_Lean_stringToMessageData(x_857);
lean_dec(x_857);
if (lean_is_scalar(x_846)) {
 x_859 = lean_alloc_ctor(7, 2, 0);
} else {
 x_859 = x_846;
 lean_ctor_set_tag(x_859, 7);
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_858);
x_860 = l_Lean_indentExpr(x_804);
if (lean_is_scalar(x_841)) {
 x_861 = lean_alloc_ctor(7, 2, 0);
} else {
 x_861 = x_841;
 lean_ctor_set_tag(x_861, 7);
}
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_860);
x_862 = lean_mk_string_unchecked("\nbut neither side of the equality is mentioned in the type", 58, 58);
x_863 = l_Lean_stringToMessageData(x_862);
lean_dec(x_862);
if (lean_is_scalar(x_837)) {
 x_864 = lean_alloc_ctor(7, 2, 0);
} else {
 x_864 = x_837;
 lean_ctor_set_tag(x_864, 7);
}
lean_ctor_set(x_864, 0, x_861);
lean_ctor_set(x_864, 1, x_863);
x_865 = l_Lean_indentExpr(x_839);
if (lean_is_scalar(x_830)) {
 x_866 = lean_alloc_ctor(7, 2, 0);
} else {
 x_866 = x_830;
 lean_ctor_set_tag(x_866, 7);
}
lean_ctor_set(x_866, 0, x_864);
lean_ctor_set(x_866, 1, x_865);
x_867 = lean_mk_string_unchecked("", 0, 0);
x_868 = l_Lean_stringToMessageData(x_867);
lean_dec(x_867);
if (lean_is_scalar(x_827)) {
 x_869 = lean_alloc_ctor(7, 2, 0);
} else {
 x_869 = x_827;
 lean_ctor_set_tag(x_869, 7);
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_868);
x_870 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_869, x_3, x_4, x_5, x_6, x_7, x_8, x_850);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_873 = x_870;
} else {
 lean_dec_ref(x_870);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_871);
lean_ctor_set(x_874, 1, x_872);
return x_874;
}
else
{
lean_object* x_875; 
lean_dec(x_851);
lean_dec(x_846);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_804);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_875 = l_Lean_Meta_mkEqSymm(x_797, x_5, x_6, x_7, x_8, x_850);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = lean_box(0);
x_879 = l_Lean_Elab_Term_elabSubst___lam__3(x_832, x_835, x_849, x_876, x_829, x_828, x_878, x_3, x_4, x_5, x_6, x_7, x_8, x_877);
lean_dec(x_828);
return x_879;
}
else
{
lean_dec(x_849);
lean_dec(x_835);
lean_dec(x_832);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_875;
}
}
}
else
{
lean_dec(x_846);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_804);
lean_dec(x_797);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_848;
}
}
else
{
lean_object* x_880; lean_object* x_881; 
lean_dec(x_846);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_804);
x_880 = lean_box(0);
x_881 = l_Lean_Elab_Term_elabSubst___lam__3(x_832, x_835, x_844, x_797, x_828, x_829, x_880, x_3, x_4, x_5, x_6, x_7, x_8, x_845);
lean_dec(x_829);
return x_881;
}
}
else
{
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_804);
lean_dec(x_797);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_843;
}
}
else
{
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_804);
lean_dec(x_797);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_838;
}
}
else
{
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_804);
lean_dec(x_797);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_834;
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_11, 0);
lean_inc(x_882);
x_883 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_829);
lean_inc(x_882);
x_884 = l_Lean_Meta_kabstract(x_882, x_829, x_883, x_5, x_6, x_7, x_8, x_825);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; uint8_t x_888; 
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
x_888 = l_Lean_Expr_hasLooseBVars(x_885);
if (x_888 == 0)
{
lean_object* x_889; 
lean_dec(x_885);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_828);
lean_inc(x_882);
x_889 = l_Lean_Meta_kabstract(x_882, x_828, x_883, x_5, x_6, x_7, x_8, x_886);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_892 = x_889;
} else {
 lean_dec_ref(x_889);
 x_892 = lean_box(0);
}
x_893 = l_Lean_Expr_hasLooseBVars(x_890);
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
lean_dec(x_890);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_894 = lean_mk_string_unchecked("invalid `▸` notation, expected result type of cast is ", 56, 54);
x_895 = l_Lean_stringToMessageData(x_894);
lean_dec(x_894);
x_896 = l_Lean_indentExpr(x_882);
if (lean_is_scalar(x_892)) {
 x_897 = lean_alloc_ctor(7, 2, 0);
} else {
 x_897 = x_892;
 lean_ctor_set_tag(x_897, 7);
}
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set(x_897, 1, x_896);
x_898 = lean_mk_string_unchecked("\nhowever, the equality ", 23, 23);
x_899 = l_Lean_stringToMessageData(x_898);
lean_dec(x_898);
if (lean_is_scalar(x_887)) {
 x_900 = lean_alloc_ctor(7, 2, 0);
} else {
 x_900 = x_887;
 lean_ctor_set_tag(x_900, 7);
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_899);
x_901 = l_Lean_indentExpr(x_797);
if (lean_is_scalar(x_830)) {
 x_902 = lean_alloc_ctor(7, 2, 0);
} else {
 x_902 = x_830;
 lean_ctor_set_tag(x_902, 7);
}
lean_ctor_set(x_902, 0, x_900);
lean_ctor_set(x_902, 1, x_901);
x_903 = lean_mk_string_unchecked("\nof type ", 9, 9);
x_904 = l_Lean_stringToMessageData(x_903);
lean_dec(x_903);
if (lean_is_scalar(x_827)) {
 x_905 = lean_alloc_ctor(7, 2, 0);
} else {
 x_905 = x_827;
 lean_ctor_set_tag(x_905, 7);
}
lean_ctor_set(x_905, 0, x_902);
lean_ctor_set(x_905, 1, x_904);
x_906 = l_Lean_indentExpr(x_804);
if (lean_is_scalar(x_806)) {
 x_907 = lean_alloc_ctor(7, 2, 0);
} else {
 x_907 = x_806;
 lean_ctor_set_tag(x_907, 7);
}
lean_ctor_set(x_907, 0, x_905);
lean_ctor_set(x_907, 1, x_906);
x_908 = lean_mk_string_unchecked("\ndoes not contain the expected result type on either the left or the right hand side", 84, 84);
x_909 = l_Lean_stringToMessageData(x_908);
lean_dec(x_908);
if (lean_is_scalar(x_802)) {
 x_910 = lean_alloc_ctor(7, 2, 0);
} else {
 x_910 = x_802;
 lean_ctor_set_tag(x_910, 7);
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_909);
x_911 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_910, x_3, x_4, x_5, x_6, x_7, x_8, x_891);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_914 = x_911;
} else {
 lean_dec_ref(x_911);
 x_914 = lean_box(0);
}
if (lean_is_scalar(x_914)) {
 x_915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_915 = x_914;
}
lean_ctor_set(x_915, 0, x_912);
lean_ctor_set(x_915, 1, x_913);
return x_915;
}
else
{
lean_object* x_916; 
lean_dec(x_892);
lean_dec(x_887);
lean_dec(x_882);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_916 = l_Lean_Meta_mkEqSymm(x_797, x_5, x_6, x_7, x_8, x_891);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; uint8_t x_920; lean_object* x_921; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec(x_916);
x_919 = lean_box(0);
x_920 = lean_unbox(x_26);
lean_inc(x_833);
x_921 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_833, x_23, x_832, x_13, x_14, x_15, x_16, x_11, x_1, x_833, x_920, x_33, x_883, x_890, x_917, x_829, x_828, x_919, x_3, x_4, x_5, x_6, x_7, x_8, x_918);
return x_921;
}
else
{
lean_dec(x_890);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_916;
}
}
}
else
{
lean_dec(x_887);
lean_dec(x_882);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_797);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_889;
}
}
else
{
lean_object* x_922; uint8_t x_923; lean_object* x_924; 
lean_dec(x_887);
lean_dec(x_882);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
x_922 = lean_box(0);
x_923 = lean_unbox(x_26);
lean_inc(x_833);
x_924 = l_Lean_Elab_Term_elabSubst___lam__6(x_32, x_833, x_23, x_832, x_13, x_14, x_15, x_16, x_11, x_1, x_833, x_923, x_33, x_883, x_885, x_797, x_828, x_829, x_922, x_3, x_4, x_5, x_6, x_7, x_8, x_886);
return x_924;
}
}
else
{
lean_dec(x_882);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_797);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_884;
}
}
}
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_797);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_925 = lean_ctor_get(x_807, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_807, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_927 = x_807;
} else {
 lean_dec_ref(x_807);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
}
else
{
lean_dec(x_797);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_799;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_39;
}
}
else
{
uint8_t x_929; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_929 = !lean_is_exclusive(x_29);
if (x_929 == 0)
{
return x_29;
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_29, 0);
x_931 = lean_ctor_get(x_29, 1);
lean_inc(x_931);
lean_inc(x_930);
lean_dec(x_29);
x_932 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
return x_932;
}
}
}
}
}
else
{
uint8_t x_933; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_933 = !lean_is_exclusive(x_10);
if (x_933 == 0)
{
return x_10;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_934 = lean_ctor_get(x_10, 0);
x_935 = lean_ctor_get(x_10, 1);
lean_inc(x_935);
lean_inc(x_934);
lean_dec(x_10);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_934);
lean_ctor_set(x_936, 1, x_935);
return x_936;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Term_elabSubst___lam__0(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Term_elabSubst___lam__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_elabSubst___lam__2(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_elabSubst___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__4___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l_Lean_Elab_Term_elabSubst___lam__4(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__5___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_7);
lean_dec(x_7);
x_21 = lean_unbox(x_10);
lean_dec(x_10);
x_22 = l_Lean_Elab_Term_elabSubst___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSubst___lam__6___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_unbox(x_3);
lean_dec(x_3);
x_28 = lean_unbox(x_12);
lean_dec(x_12);
x_29 = l_Lean_Elab_Term_elabSubst___lam__6(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_19);
return x_29;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("subst", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabSubst", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabSubst", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(344u);
x_8 = lean_unsigned_to_nat(27u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(422u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_unsigned_to_nat(40u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_elabType(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_61 = lean_unsigned_to_nat(2u);
x_62 = l_Lean_Syntax_getArg(x_1, x_61);
lean_inc(x_62);
x_63 = l_Lean_Syntax_getKind(x_62);
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Parser", 6, 6);
x_66 = lean_mk_string_unchecked("Term", 4, 4);
x_67 = lean_mk_string_unchecked("macroDollarArg", 14, 14);
x_68 = l_Lean_Name_mkStr4(x_64, x_65, x_66, x_67);
x_69 = lean_name_eq(x_63, x_68);
lean_dec(x_68);
lean_dec(x_63);
if (x_69 == 0)
{
x_14 = x_62;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_60;
}
else
{
lean_object* x_70; 
x_70 = l_Lean_Syntax_getArg(x_62, x_9);
lean_dec(x_62);
x_14 = x_70;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_60;
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_21 = l_Lean_levelOne;
x_22 = l_Lean_Expr_sort___override(x_21);
lean_inc_n(x_22, 2);
x_23 = l_Lean_mkArrow(x_22, x_22, x_19, x_20, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = lean_unbox(x_27);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_30 = l_Lean_Elab_Term_elabTerm(x_14, x_26, x_28, x_29, x_15, x_16, x_17, x_18, x_19, x_20, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_22);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = lean_unbox(x_34);
lean_inc(x_17);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_33, x_36, x_35, x_17, x_18, x_19, x_20, x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_mk_string_unchecked("STWorld", 7, 7);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
lean_inc(x_38);
x_44 = lean_array_push(x_43, x_38);
lean_inc(x_31);
x_45 = lean_array_push(x_44, x_31);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_46 = l_Lean_Meta_mkAppM(x_41, x_45, x_17, x_18, x_19, x_20, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_50 = l_Lean_Elab_Term_mkInstMVar(x_47, x_49, x_15, x_16, x_17, x_18, x_19, x_20, x_48);
lean_dec(x_16);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("StateRefT'", 10, 10);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_mk_empty_array_with_capacity(x_54);
x_56 = lean_array_push(x_55, x_38);
x_57 = lean_array_push(x_56, x_12);
x_58 = lean_array_push(x_57, x_31);
x_59 = l_Lean_Meta_mkAppM(x_53, x_58, x_17, x_18, x_19, x_20, x_51);
return x_59;
}
else
{
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
return x_50;
}
}
else
{
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
return x_46;
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
return x_30;
}
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
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabStateRefT___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabStateRefT___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabStateRefT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("stateRefT", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabStateRefT", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStateRefT___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabStateRefT", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(424u);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(433u);
x_11 = lean_unsigned_to_nat(32u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoindex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = lean_unbox(x_12);
x_15 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoindex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabNoindex(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("noindex", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabNoindex", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNoindex___boxed), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabNoindex", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(435u);
x_8 = lean_unsigned_to_nat(29u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(437u);
x_11 = lean_unsigned_to_nat(40u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(33u);
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_elabUnsafe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_setImplementedBy(x_13, x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_ctor_set_tag(x_14, 3);
x_16 = l_Lean_MessageData_ofFormat(x_14);
x_17 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0_spec__0___redArg(x_22, x_6, x_8, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("Lean.Elab.BuiltinNotation", 25, 25);
x_10 = lean_mk_string_unchecked("Lean.Elab.Term.elabUnsafe", 25, 25);
x_11 = lean_unsigned_to_nat(516u);
x_12 = lean_unsigned_to_nat(54u);
x_13 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_14 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_15 = l_panic___at___Lean_Elab_Term_elabUnsafe_spec__0(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_elabTermAndSynthesize(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
x_22 = l_Lean_Meta_getMVars(x_20, x_5, x_6, x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_23, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = l_Lean_Name_mkStr1(x_13);
lean_inc(x_3);
x_32 = l_Lean_Elab_Term_mkAuxName(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unbox(x_27);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Lean_Meta_mkAuxDefinitionFor(x_33, x_20, x_35, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_getAppFn(x_37);
switch (lean_obj_tag(x_39)) {
case 0:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Expr_bvar___override(x_40);
x_42 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_41);
return x_42;
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_Expr_fvar___override(x_43);
x_45 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_44);
return x_45;
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = l_Lean_Expr_mvar___override(x_46);
x_48 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_47);
return x_48;
}
case 3:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = l_Lean_Expr_sort___override(x_49);
x_51 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_50);
return x_51;
}
case 4:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
lean_inc(x_3);
lean_inc(x_52);
x_54 = l_Lean_getConstInfo___at___Lean_getConstInfoCtor___at___Lean_Elab_Term_elabAnonymousCtor_spec__0_spec__0(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_mk_string_unchecked("unsafe_impl", 11, 11);
x_60 = l_Lean_Name_mkStr1(x_59);
lean_inc(x_3);
x_61 = l_Lean_Elab_Term_mkAuxName(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_64, 2);
lean_inc(x_65);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_65);
x_66 = l_Lean_Meta_mkOfNonempty(x_65, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
lean_inc(x_62);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_65);
x_72 = lean_box(0);
x_73 = lean_box(1);
lean_inc(x_62);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 0, x_62);
x_74 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_72);
lean_ctor_set(x_74, 3, x_66);
x_75 = lean_unbox(x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_75);
lean_ctor_set(x_55, 0, x_74);
lean_inc(x_8);
lean_inc(x_7);
x_76 = l_Lean_addDecl(x_55, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_62);
x_78 = l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(x_62, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = l_Lean_Expr_const___override(x_62, x_53);
x_82 = lean_box(0);
x_83 = l_Lean_Expr_sort___override(x_82);
x_84 = l_Lean_Expr_getAppNumArgs(x_37);
lean_inc(x_84);
x_85 = lean_mk_array(x_84, x_83);
x_86 = lean_nat_sub(x_84, x_17);
lean_dec(x_84);
x_87 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_37, x_85, x_86);
x_88 = l_Lean_mkAppN(x_81, x_87);
lean_dec(x_87);
lean_ctor_set(x_78, 0, x_88);
return x_78;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
lean_dec(x_78);
x_90 = l_Lean_Expr_const___override(x_62, x_53);
x_91 = lean_box(0);
x_92 = l_Lean_Expr_sort___override(x_91);
x_93 = l_Lean_Expr_getAppNumArgs(x_37);
lean_inc(x_93);
x_94 = lean_mk_array(x_93, x_92);
x_95 = lean_nat_sub(x_93, x_17);
lean_dec(x_93);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_37, x_94, x_95);
x_97 = l_Lean_mkAppN(x_90, x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_89);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_37);
x_99 = !lean_is_exclusive(x_78);
if (x_99 == 0)
{
return x_78;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_78, 0);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_78);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_76);
if (x_103 == 0)
{
return x_76;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_76, 0);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_76);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_66, 0);
x_108 = lean_ctor_get(x_66, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_66);
x_109 = lean_ctor_get(x_64, 1);
lean_inc(x_109);
lean_dec(x_64);
lean_inc(x_62);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_62);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_65);
x_111 = lean_box(0);
x_112 = lean_box(1);
lean_inc(x_62);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_62);
lean_ctor_set(x_113, 1, x_29);
x_114 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_unbox(x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_115);
lean_ctor_set(x_55, 0, x_114);
lean_inc(x_8);
lean_inc(x_7);
x_116 = l_Lean_addDecl(x_55, x_7, x_8, x_108);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_62);
x_118 = l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(x_62, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Expr_const___override(x_62, x_53);
x_122 = lean_box(0);
x_123 = l_Lean_Expr_sort___override(x_122);
x_124 = l_Lean_Expr_getAppNumArgs(x_37);
lean_inc(x_124);
x_125 = lean_mk_array(x_124, x_123);
x_126 = lean_nat_sub(x_124, x_17);
lean_dec(x_124);
x_127 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_37, x_125, x_126);
x_128 = l_Lean_mkAppN(x_121, x_127);
lean_dec(x_127);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_120;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_119);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_37);
x_130 = lean_ctor_get(x_118, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_132 = x_118;
} else {
 lean_dec_ref(x_118);
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
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_116, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_116, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_136 = x_116;
} else {
 lean_dec_ref(x_116);
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
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_free_object(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_55, 0);
lean_inc(x_138);
lean_dec(x_55);
x_139 = lean_mk_string_unchecked("unsafe_impl", 11, 11);
x_140 = l_Lean_Name_mkStr1(x_139);
lean_inc(x_3);
x_141 = l_Lean_Elab_Term_mkAuxName(x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_ctor_get(x_144, 2);
lean_inc(x_145);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_145);
x_146 = l_Lean_Meta_mkOfNonempty(x_145, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec(x_144);
lean_inc(x_142);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_145);
x_152 = lean_box(0);
x_153 = lean_box(1);
lean_inc(x_142);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_149;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_29);
x_155 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_152);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_unbox(x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_156);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_155);
lean_inc(x_8);
lean_inc(x_7);
x_158 = l_Lean_addDecl(x_157, x_7, x_8, x_148);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_inc(x_142);
x_160 = l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(x_142, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = l_Lean_Expr_const___override(x_142, x_53);
x_164 = lean_box(0);
x_165 = l_Lean_Expr_sort___override(x_164);
x_166 = l_Lean_Expr_getAppNumArgs(x_37);
lean_inc(x_166);
x_167 = lean_mk_array(x_166, x_165);
x_168 = lean_nat_sub(x_166, x_17);
lean_dec(x_166);
x_169 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_37, x_167, x_168);
x_170 = l_Lean_mkAppN(x_163, x_169);
lean_dec(x_169);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_161);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_142);
lean_dec(x_53);
lean_dec(x_37);
x_172 = lean_ctor_get(x_160, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_160, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_174 = x_160;
} else {
 lean_dec_ref(x_160);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_142);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_ctor_get(x_158, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_178 = x_158;
} else {
 lean_dec_ref(x_158);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
x_180 = lean_ctor_get(x_54, 1);
lean_inc(x_180);
lean_dec(x_54);
x_181 = lean_mk_string_unchecked("Lean.Elab.BuiltinNotation", 25, 25);
x_182 = lean_mk_string_unchecked("Lean.Elab.Term.elabUnsafe", 25, 25);
x_183 = lean_unsigned_to_nat(517u);
x_184 = lean_unsigned_to_nat(55u);
x_185 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_186 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_181, x_182, x_183, x_184, x_185);
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_181);
x_187 = l_panic___at___Lean_Elab_Term_elabUnsafe_spec__0(x_186, x_3, x_4, x_5, x_6, x_7, x_8, x_180);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = !lean_is_exclusive(x_54);
if (x_188 == 0)
{
return x_54;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_54, 0);
x_190 = lean_ctor_get(x_54, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_54);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 5:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_37);
x_192 = lean_ctor_get(x_39, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_39, 1);
lean_inc(x_193);
lean_dec(x_39);
x_194 = l_Lean_Expr_app___override(x_192, x_193);
x_195 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_194);
return x_195;
}
case 6:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_37);
x_196 = lean_ctor_get(x_39, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_39, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_39, 2);
lean_inc(x_198);
x_199 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 8);
lean_dec(x_39);
x_200 = l_Lean_Expr_lam___override(x_196, x_197, x_198, x_199);
x_201 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_200, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_200);
return x_201;
}
case 7:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_37);
x_202 = lean_ctor_get(x_39, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_39, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_39, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 8);
lean_dec(x_39);
x_206 = l_Lean_Expr_forallE___override(x_202, x_203, x_204, x_205);
x_207 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_206);
return x_207;
}
case 8:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_37);
x_208 = lean_ctor_get(x_39, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_39, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_39, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_39, 3);
lean_inc(x_211);
x_212 = lean_ctor_get_uint8(x_39, sizeof(void*)*4 + 8);
lean_dec(x_39);
x_213 = l_Lean_Expr_letE___override(x_208, x_209, x_210, x_211, x_212);
x_214 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_213, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_213);
return x_214;
}
case 9:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_37);
x_215 = lean_ctor_get(x_39, 0);
lean_inc(x_215);
lean_dec(x_39);
x_216 = l_Lean_Expr_lit___override(x_215);
x_217 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_216);
return x_217;
}
case 10:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_37);
x_218 = lean_ctor_get(x_39, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_39, 1);
lean_inc(x_219);
lean_dec(x_39);
x_220 = l_Lean_Expr_mdata___override(x_218, x_219);
x_221 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_220, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_220);
return x_221;
}
default: 
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_37);
x_222 = lean_ctor_get(x_39, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_39, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_39, 2);
lean_inc(x_224);
lean_dec(x_39);
x_225 = l_Lean_Expr_proj___override(x_222, x_223, x_224);
x_226 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_225, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_225);
return x_226;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
}
else
{
lean_object* x_227; uint8_t x_228; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_227 = l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwMVarError_spec__0___redArg(x_28);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
return x_227;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_227);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_232 = !lean_is_exclusive(x_26);
if (x_232 == 0)
{
return x_26;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_26, 0);
x_234 = lean_ctor_get(x_26, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_26);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_setImplementedBy___at___Lean_Elab_Term_elabUnsafe_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabUnsafe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabUnsafe___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabUnsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabUnsafe", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabUnsafe), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabUnsafe_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabUnsafe", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(440u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(460u);
x_11 = lean_unsigned_to_nat(31u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_9 = lean_mk_string_unchecked("x", 1, 1);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_string_unchecked("Option", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Expr", 4, 4);
lean_inc(x_16);
x_18 = l_Lean_Name_mkStr2(x_16, x_17);
x_19 = l_Lean_Expr_const___override(x_18, x_14);
lean_inc(x_19);
x_20 = l_Lean_Expr_app___override(x_15, x_19);
x_21 = lean_mk_string_unchecked("Elab", 4, 4);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("TermElabM", 9, 9);
x_24 = l_Lean_Name_mkStr4(x_16, x_21, x_22, x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_14);
x_26 = l_Lean_Expr_app___override(x_25, x_19);
x_27 = lean_unbox(x_11);
x_28 = l_Lean_Expr_forallE___override(x_10, x_20, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Elab_Term_evalTerm___redArg(x_28, x_1, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab_unsafe__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("TermElabM", 9, 9);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("Expr", 4, 4);
x_17 = l_Lean_Name_mkStr2(x_9, x_16);
x_18 = l_Lean_Expr_const___override(x_17, x_14);
x_19 = l_Lean_Expr_app___override(x_15, x_18);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Elab_Term_evalTerm___redArg(x_19, x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabRunElab_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRunElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("byElab", 6, 6);
lean_inc(x_10);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("Parser", 6, 6);
x_18 = lean_mk_string_unchecked("Term", 4, 4);
x_63 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_64 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_63);
lean_inc(x_16);
x_65 = l_Lean_Syntax_isOfKind(x_16, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_Syntax_getArg(x_16, x_66);
lean_inc(x_67);
x_68 = l_Lean_Syntax_matchesNull(x_67, x_15);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = l_Lean_Syntax_getArg(x_67, x_66);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_71 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_70);
lean_inc(x_69);
x_72 = l_Lean_Syntax_isOfKind(x_69, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = l_Lean_Syntax_getArg(x_69, x_66);
x_74 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_75 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_74);
lean_inc(x_73);
x_76 = l_Lean_Syntax_isOfKind(x_73, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Syntax_getArg(x_69, x_15);
lean_dec(x_69);
x_78 = l_Lean_Syntax_matchesNull(x_77, x_66);
if (x_78 == 0)
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_64);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = l_Lean_Syntax_getArg(x_73, x_66);
lean_dec(x_73);
lean_inc(x_79);
x_80 = l_Lean_Syntax_isOfKind(x_79, x_64);
lean_dec(x_64);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
uint8_t x_90; lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Syntax_getArg(x_79, x_66);
lean_inc(x_92);
x_93 = l_Lean_Syntax_matchesNull(x_92, x_15);
if (x_93 == 0)
{
lean_dec(x_92);
lean_dec(x_75);
lean_dec(x_71);
x_90 = x_93;
goto block_91;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Lean_Syntax_getArg(x_92, x_66);
lean_dec(x_92);
lean_inc(x_94);
x_95 = l_Lean_Syntax_isOfKind(x_94, x_71);
lean_dec(x_71);
if (x_95 == 0)
{
lean_dec(x_94);
lean_dec(x_75);
x_90 = x_95;
goto block_91;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_Syntax_getArg(x_94, x_66);
lean_inc(x_96);
x_97 = l_Lean_Syntax_isOfKind(x_96, x_75);
lean_dec(x_75);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
x_90 = x_97;
goto block_91;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = l_Lean_Syntax_getArg(x_96, x_66);
lean_dec(x_96);
x_99 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_100 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_99);
lean_inc(x_98);
x_101 = l_Lean_Syntax_isOfKind(x_98, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_dec(x_98);
lean_dec(x_94);
x_90 = x_101;
goto block_91;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = l_Lean_Syntax_getArg(x_98, x_15);
lean_dec(x_98);
x_103 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_104 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_103);
lean_inc(x_102);
x_105 = l_Lean_Syntax_isOfKind(x_102, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec(x_102);
lean_dec(x_94);
x_90 = x_105;
goto block_91;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_Syntax_getArg(x_102, x_15);
lean_dec(x_102);
x_107 = l_Lean_Syntax_matchesNull(x_106, x_66);
if (x_107 == 0)
{
lean_dec(x_94);
x_90 = x_107;
goto block_91;
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = l_Lean_Syntax_getArg(x_94, x_15);
lean_dec(x_94);
x_109 = l_Lean_Syntax_matchesNull(x_108, x_66);
if (x_109 == 0)
{
x_90 = x_109;
goto block_91;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
goto block_89;
}
}
}
}
}
}
}
block_89:
{
lean_object* x_81; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l_Lean_Elab_Term_elabRunElab_unsafe__1(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_apply_8(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_91:
{
if (x_90 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_62;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
goto block_89;
}
}
}
}
}
}
}
}
block_62:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_st_ref_get(x_24, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 5);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
lean_dec(x_30);
x_34 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_34);
x_35 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_34);
lean_inc(x_33);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_33);
x_36 = l_Lean_Syntax_node2(x_33, x_35, x_26, x_16);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_37 = l_Lean_Elab_Term_elabRunElab_unsafe__2(x_36, x_19, x_20, x_21, x_22, x_23, x_24, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_apply_7(x_38, x_19, x_20, x_21, x_22, x_23, x_24, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_dec(x_26);
x_46 = lean_ctor_get(x_23, 5);
lean_inc(x_46);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_SourceInfo_fromRef(x_46, x_48);
lean_dec(x_46);
x_50 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_50);
x_51 = l_Lean_Name_mkStr4(x_10, x_17, x_18, x_50);
lean_inc(x_49);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Syntax_node2(x_49, x_51, x_52, x_16);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_54 = l_Lean_Elab_Term_elabRunElab_unsafe__2(x_53, x_19, x_20, x_21, x_22, x_23, x_24, x_45);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_apply_7(x_55, x_19, x_20, x_21, x_22, x_23, x_24, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabRunElab_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabRunElab_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("byElab", 6, 6);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("elabRunElab", 11, 11);
x_9 = l_Lean_Name_mkStr4(x_3, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRunElab), 9, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_5, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabRunElab", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elaborator for `by_elab`. ", 26, 26);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRunElab_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabRunElab", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(463u);
x_8 = lean_unsigned_to_nat(28u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(476u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(43u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Term_elabType(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_box(0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_15, x_3, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_box(1);
x_22 = lean_unbox(x_20);
x_23 = lean_unbox(x_21);
x_24 = l_Lean_Meta_mkForallFVars(x_4, x_13, x_22, x_3, x_23, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unbox(x_20);
x_28 = lean_unbox(x_20);
x_29 = lean_unbox(x_21);
x_30 = l_Lean_Meta_mkLambdaFVars(x_4, x_18, x_27, x_3, x_28, x_29, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Elab_Term_elabTerm(x_2, x_14, x_3, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_18);
x_19 = lean_array_push(x_18, x_6);
x_20 = l_Lean_Expr_abstractM(x_16, x_19, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_push(x_18, x_5);
x_24 = lean_expr_instantiate(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_array_push(x_18, x_5);
x_28 = lean_expr_instantiate(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_dec(x_18);
lean_dec(x_5);
return x_20;
}
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Elab_Term_elabBinders(lean_box(0), x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI___lam__1___boxed), 13, 5);
lean_closure_set(x_21, 0, x_7);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_19);
x_22 = l_Lean_Syntax_getId(x_6);
x_23 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_withLocalIdentFor_spec__0___redArg(x_22, x_18, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("haveI", 5, 5);
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
x_19 = lean_mk_string_unchecked("haveDecl", 8, 8);
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
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_25 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_26 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_25);
lean_inc(x_24);
x_27 = l_Lean_Syntax_isOfKind(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
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
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArg(x_24, x_23);
x_30 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_30);
lean_inc(x_29);
x_32 = l_Lean_Syntax_isOfKind(x_29, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_24);
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
x_33 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArg(x_29, x_23);
lean_dec(x_29);
x_35 = lean_mk_string_unchecked("ident", 5, 5);
x_36 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_34);
x_37 = l_Lean_Syntax_isOfKind(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_24);
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
x_38 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_24, x_39);
lean_inc(x_40);
x_41 = l_Lean_Syntax_matchesNull(x_40, x_17);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_24);
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
x_42 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_Syntax_getArg(x_40, x_23);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_45 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_44);
lean_inc(x_43);
x_46 = l_Lean_Syntax_isOfKind(x_43, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_Lean_Syntax_getArg(x_24, x_17);
x_49 = l_Lean_Syntax_getArg(x_43, x_17);
lean_dec(x_43);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_unsigned_to_nat(4u);
x_52 = l_Lean_Syntax_getArg(x_24, x_51);
lean_dec(x_24);
x_53 = lean_box(x_46);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI___lam__0___boxed), 11, 3);
lean_closure_set(x_54, 0, x_49);
lean_closure_set(x_54, 1, x_52);
lean_closure_set(x_54, 2, x_53);
x_55 = l_Lean_Syntax_getArg(x_1, x_50);
lean_dec(x_1);
x_56 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_57 = lean_box(x_46);
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI___lam__2___boxed), 14, 6);
lean_closure_set(x_58, 0, x_56);
lean_closure_set(x_58, 1, x_54);
lean_closure_set(x_58, 2, x_55);
lean_closure_set(x_58, 3, x_57);
lean_closure_set(x_58, 4, x_17);
lean_closure_set(x_58, 5, x_34);
x_59 = l_Lean_Elab_Term_withExpectedType(x_2, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_59;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Term_elabHaveI___lam__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Term_elabHaveI___lam__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveI___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Term_elabHaveI___lam__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHaveI__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("haveI", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabHaveI", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHaveI_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabHaveI", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(478u);
x_8 = lean_unsigned_to_nat(44u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(488u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(48u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Elab_Term_elabBinders(lean_box(0), x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(x_4);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI___lam__1___boxed), 13, 5);
lean_closure_set(x_21, 0, x_7);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_19);
x_22 = l_Lean_Syntax_getId(x_6);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__1___redArg(x_22, x_18, x_19, x_21, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("letI", 4, 4);
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
x_19 = lean_mk_string_unchecked("haveDecl", 8, 8);
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
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_25 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_26 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_25);
lean_inc(x_24);
x_27 = l_Lean_Syntax_isOfKind(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
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
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArg(x_24, x_23);
x_30 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_30);
lean_inc(x_29);
x_32 = l_Lean_Syntax_isOfKind(x_29, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_24);
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
x_33 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArg(x_29, x_23);
lean_dec(x_29);
x_35 = lean_mk_string_unchecked("ident", 5, 5);
x_36 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_34);
x_37 = l_Lean_Syntax_isOfKind(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_24);
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
x_38 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_24, x_39);
lean_inc(x_40);
x_41 = l_Lean_Syntax_matchesNull(x_40, x_17);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_24);
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
x_42 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_Syntax_getArg(x_40, x_23);
lean_dec(x_40);
x_44 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_45 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_44);
lean_inc(x_43);
x_46 = l_Lean_Syntax_isOfKind(x_43, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_Lean_Syntax_getArg(x_24, x_17);
x_49 = l_Lean_Syntax_getArg(x_43, x_17);
lean_dec(x_43);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_unsigned_to_nat(4u);
x_52 = l_Lean_Syntax_getArg(x_24, x_51);
lean_dec(x_24);
x_53 = lean_box(x_46);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveI___lam__0___boxed), 11, 3);
lean_closure_set(x_54, 0, x_49);
lean_closure_set(x_54, 1, x_52);
lean_closure_set(x_54, 2, x_53);
x_55 = l_Lean_Syntax_getArg(x_1, x_50);
lean_dec(x_1);
x_56 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_57 = lean_box(x_46);
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetI___lam__2___boxed), 14, 6);
lean_closure_set(x_58, 0, x_56);
lean_closure_set(x_58, 1, x_54);
lean_closure_set(x_58, 2, x_55);
lean_closure_set(x_58, 3, x_57);
lean_closure_set(x_58, 4, x_17);
lean_closure_set(x_58, 5, x_34);
x_59 = l_Lean_Elab_Term_withExpectedType(x_2, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_59;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetI___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Term_elabLetI___lam__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetI__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("letI", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabLetI", 8, 8);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetI), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetI_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabLetI", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(490u);
x_8 = lean_unsigned_to_nat(43u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(500u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(47u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(55u);
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
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoe__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoe_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoeFunNotation_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCoeSortNotation_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabBorrowed__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabBorrowed_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandShow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandShow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabShow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabShow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandHave__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandHave_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandSuffices__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandSuffices_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabPanic__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabPanic_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandUnreachable__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandUnreachable_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandAssert__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandAssert_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_BuiltinNotation___hyg_8333_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_debugAssertions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_debugAssertions);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabDebugAssert__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandDbgTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandDbgTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabSorry__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabSorry_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandParen__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandParen_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandTuple__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandTuple_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandTypeAscription__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandTypeAscription_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabTypeAscription__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabTypeAscription_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabSubst__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabSubst_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabStateRefT__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabStateRefT_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabNoindex__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabNoindex_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabUnsafe__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabUnsafe_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabRunElab__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabRunElab_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabRunElab_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabHaveI__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabHaveI_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetI__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabLetI_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
