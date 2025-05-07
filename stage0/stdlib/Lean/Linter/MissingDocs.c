// Lean compiler output
// Module: Lean.Linter.MissingDocs
// Imports: Lean.Parser.Syntax Lean.Meta.Tactic.Simp.RegisterCommand Lean.Elab.Command Lean.Elab.SetOption Lean.Linter.Util
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
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_772_(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocsExt;
lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterMissingDocs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1___redArg(lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterMissingDocs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_329_(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs;
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_missingDocs;
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_lintNamed___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_MissingDocs___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_getHandlers(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___lam__0___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(uint8_t, uint8_t);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
size_t lean_usize_sub(size_t, size_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_builtinHandlersRef;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn____x40_Lean_Linter_MissingDocs___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("linter", 6, 6);
x_3 = lean_mk_string_unchecked("missingDocs", 11, 11);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("enable the 'missing documentation' linter", 41, 41);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Linter", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_9, x_10, x_2, x_3);
x_12 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_4, x_8, x_11, x_1);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterMissingDocs(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Linter_linter_missingDocs;
x_3 = l_Lean_Linter_getLinterValue(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterMissingDocs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_getLinterMissingDocs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("unexpected missing docs handler at '", 36, 36);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_1, x_8, x_2);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("', `MissingDocs.Handler` or `MissingDocs.SimpleHandler` expected", 64, 64);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_1);
lean_inc(x_4);
x_7 = l_Lean_Environment_find_x3f(x_4, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0___boxed), 1, 0);
x_9 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_1, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("'", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0___boxed), 1, 0);
x_20 = l_Lean_ConstantInfo_type(x_18);
lean_dec(x_18);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_bvar___override(x_21);
x_23 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_22, x_2, x_3);
lean_dec(x_2);
lean_dec(x_22);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Expr_fvar___override(x_24);
x_26 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_25, x_2, x_3);
lean_dec(x_2);
lean_dec(x_25);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Expr_mvar___override(x_27);
x_29 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_28, x_2, x_3);
lean_dec(x_2);
lean_dec(x_28);
return x_29;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Expr_sort___override(x_30);
x_32 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_31, x_2, x_3);
lean_dec(x_2);
lean_dec(x_31);
return x_32;
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_box(0);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_36 = l_Lean_Expr_const___override(x_35, x_34);
x_37 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_36, x_2, x_3);
lean_dec(x_2);
lean_dec(x_36);
return x_37;
}
case 1:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l_Lean_Name_str___override(x_35, x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_34);
x_42 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_41, x_2, x_3);
lean_dec(x_2);
lean_dec(x_41);
return x_42;
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
lean_inc(x_45);
x_46 = l_Lean_Name_str___override(x_35, x_45);
switch (lean_obj_tag(x_44)) {
case 0:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_4);
x_47 = l_Lean_Name_str___override(x_46, x_43);
x_48 = l_Lean_Expr_const___override(x_47, x_34);
x_49 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_48, x_2, x_3);
lean_dec(x_2);
lean_dec(x_48);
return x_49;
}
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_46);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
lean_inc(x_51);
x_52 = l_Lean_Name_str___override(x_35, x_51);
lean_inc(x_45);
x_53 = l_Lean_Name_str___override(x_52, x_45);
switch (lean_obj_tag(x_50)) {
case 0:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_4);
x_54 = l_Lean_Name_str___override(x_53, x_43);
x_55 = l_Lean_Expr_const___override(x_54, x_34);
x_56 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_55, x_2, x_3);
lean_dec(x_2);
lean_dec(x_55);
return x_56;
}
case 1:
{
lean_object* x_57; 
lean_dec(x_53);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_string_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_4);
x_61 = l_Lean_Name_str___override(x_35, x_58);
x_62 = l_Lean_Name_str___override(x_61, x_51);
x_63 = l_Lean_Name_str___override(x_62, x_45);
x_64 = l_Lean_Name_str___override(x_63, x_43);
x_65 = l_Lean_Expr_const___override(x_64, x_34);
x_66 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_65, x_2, x_3);
lean_dec(x_2);
lean_dec(x_65);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_58);
x_67 = lean_mk_string_unchecked("Linter", 6, 6);
x_68 = lean_string_dec_eq(x_51, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_dec(x_4);
x_69 = l_Lean_Name_str___override(x_35, x_59);
x_70 = l_Lean_Name_str___override(x_69, x_51);
x_71 = l_Lean_Name_str___override(x_70, x_45);
x_72 = l_Lean_Name_str___override(x_71, x_43);
x_73 = l_Lean_Expr_const___override(x_72, x_34);
x_74 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_73, x_2, x_3);
lean_dec(x_2);
lean_dec(x_73);
return x_74;
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_51);
x_75 = lean_mk_string_unchecked("MissingDocs", 11, 11);
x_76 = lean_string_dec_eq(x_45, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
lean_dec(x_4);
x_77 = l_Lean_Name_str___override(x_35, x_59);
x_78 = l_Lean_Name_str___override(x_77, x_67);
x_79 = l_Lean_Name_str___override(x_78, x_45);
x_80 = l_Lean_Name_str___override(x_79, x_43);
x_81 = l_Lean_Expr_const___override(x_80, x_34);
x_82 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_81, x_2, x_3);
lean_dec(x_2);
lean_dec(x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_45);
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
x_84 = lean_mk_string_unchecked("SimpleHandler", 13, 13);
x_85 = lean_string_dec_eq(x_43, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_mk_string_unchecked("Handler", 7, 7);
x_87 = lean_string_dec_eq(x_43, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_83);
lean_dec(x_4);
x_88 = l_Lean_Name_str___override(x_35, x_59);
x_89 = l_Lean_Name_str___override(x_88, x_67);
x_90 = l_Lean_Name_str___override(x_89, x_75);
x_91 = l_Lean_Name_str___override(x_90, x_43);
x_92 = l_Lean_Expr_const___override(x_91, x_34);
x_93 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_92, x_2, x_3);
lean_dec(x_2);
lean_dec(x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_43);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_2);
x_94 = lean_eval_const(x_4, x_83, x_1);
lean_dec(x_1);
lean_dec(x_83);
lean_dec(x_4);
x_95 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_94, x_3);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_75);
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_43);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_2);
x_96 = lean_eval_const(x_4, x_83, x_1);
lean_dec(x_1);
lean_dec(x_83);
lean_dec(x_4);
x_97 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_96, x_3);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_100, 0, x_99);
lean_ctor_set(x_97, 0, x_100);
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
x_103 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_103, 0, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_97);
if (x_105 == 0)
{
return x_97;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_97, 0);
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_97);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_4);
x_109 = lean_ctor_get(x_50, 1);
lean_inc(x_109);
lean_dec(x_50);
x_110 = lean_ctor_get(x_57, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_57, 1);
lean_inc(x_111);
lean_dec(x_57);
x_112 = l_Lean_Name_str___override(x_110, x_111);
x_113 = l_Lean_Name_str___override(x_112, x_109);
x_114 = l_Lean_Name_str___override(x_113, x_51);
x_115 = l_Lean_Name_str___override(x_114, x_45);
x_116 = l_Lean_Name_str___override(x_115, x_43);
x_117 = l_Lean_Expr_const___override(x_116, x_34);
x_118 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_117, x_2, x_3);
lean_dec(x_2);
lean_dec(x_117);
return x_118;
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_4);
x_119 = lean_ctor_get(x_50, 1);
lean_inc(x_119);
lean_dec(x_50);
x_120 = lean_ctor_get(x_57, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_57, 1);
lean_inc(x_121);
lean_dec(x_57);
x_122 = l_Lean_Name_num___override(x_120, x_121);
x_123 = l_Lean_Name_str___override(x_122, x_119);
x_124 = l_Lean_Name_str___override(x_123, x_51);
x_125 = l_Lean_Name_str___override(x_124, x_45);
x_126 = l_Lean_Name_str___override(x_125, x_43);
x_127 = l_Lean_Expr_const___override(x_126, x_34);
x_128 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_127, x_2, x_3);
lean_dec(x_2);
lean_dec(x_127);
return x_128;
}
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_53);
lean_dec(x_4);
x_129 = lean_ctor_get(x_50, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_50, 1);
lean_inc(x_130);
lean_dec(x_50);
x_131 = l_Lean_Name_num___override(x_129, x_130);
x_132 = l_Lean_Name_str___override(x_131, x_51);
x_133 = l_Lean_Name_str___override(x_132, x_45);
x_134 = l_Lean_Name_str___override(x_133, x_43);
x_135 = l_Lean_Expr_const___override(x_134, x_34);
x_136 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_135, x_2, x_3);
lean_dec(x_2);
lean_dec(x_135);
return x_136;
}
}
}
default: 
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_46);
lean_dec(x_4);
x_137 = lean_ctor_get(x_44, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_44, 1);
lean_inc(x_138);
lean_dec(x_44);
x_139 = l_Lean_Name_num___override(x_137, x_138);
x_140 = l_Lean_Name_str___override(x_139, x_45);
x_141 = l_Lean_Name_str___override(x_140, x_43);
x_142 = l_Lean_Expr_const___override(x_141, x_34);
x_143 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_142, x_2, x_3);
lean_dec(x_2);
lean_dec(x_142);
return x_143;
}
}
}
default: 
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_4);
x_144 = lean_ctor_get(x_33, 1);
lean_inc(x_144);
lean_dec(x_33);
x_145 = lean_ctor_get(x_38, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_38, 1);
lean_inc(x_146);
lean_dec(x_38);
x_147 = l_Lean_Name_num___override(x_145, x_146);
x_148 = l_Lean_Name_str___override(x_147, x_144);
x_149 = l_Lean_Expr_const___override(x_148, x_34);
x_150 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_149, x_2, x_3);
lean_dec(x_2);
lean_dec(x_149);
return x_150;
}
}
}
default: 
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_4);
x_151 = lean_ctor_get(x_33, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_dec(x_33);
x_153 = l_Lean_Name_num___override(x_151, x_152);
x_154 = l_Lean_Expr_const___override(x_153, x_34);
x_155 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_154, x_2, x_3);
lean_dec(x_2);
lean_dec(x_154);
return x_155;
}
}
}
case 5:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_4);
x_156 = lean_ctor_get(x_20, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_20, 1);
lean_inc(x_157);
lean_dec(x_20);
x_158 = l_Lean_Expr_app___override(x_156, x_157);
x_159 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_158, x_2, x_3);
lean_dec(x_2);
lean_dec(x_158);
return x_159;
}
case 6:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_4);
x_160 = lean_ctor_get(x_20, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_20, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_20, 2);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_164 = l_Lean_Expr_lam___override(x_160, x_161, x_162, x_163);
x_165 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_164, x_2, x_3);
lean_dec(x_2);
lean_dec(x_164);
return x_165;
}
case 7:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_4);
x_166 = lean_ctor_get(x_20, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_20, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_20, 2);
lean_inc(x_168);
x_169 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_170 = l_Lean_Expr_forallE___override(x_166, x_167, x_168, x_169);
x_171 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_170, x_2, x_3);
lean_dec(x_2);
lean_dec(x_170);
return x_171;
}
case 8:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_4);
x_172 = lean_ctor_get(x_20, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_20, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_20, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_20, 3);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_20, sizeof(void*)*4 + 8);
lean_dec(x_20);
x_177 = l_Lean_Expr_letE___override(x_172, x_173, x_174, x_175, x_176);
x_178 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_177, x_2, x_3);
lean_dec(x_2);
lean_dec(x_177);
return x_178;
}
case 9:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_4);
x_179 = lean_ctor_get(x_20, 0);
lean_inc(x_179);
lean_dec(x_20);
x_180 = l_Lean_Expr_lit___override(x_179);
x_181 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_180, x_2, x_3);
lean_dec(x_2);
lean_dec(x_180);
return x_181;
}
case 10:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_4);
x_182 = lean_ctor_get(x_20, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_20, 1);
lean_inc(x_183);
lean_dec(x_20);
x_184 = l_Lean_Expr_mdata___override(x_182, x_183);
x_185 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_184, x_2, x_3);
lean_dec(x_2);
lean_dec(x_184);
return x_185;
}
default: 
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_4);
x_186 = lean_ctor_get(x_20, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_20, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_20, 2);
lean_inc(x_188);
lean_dec(x_20);
x_189 = l_Lean_Expr_proj___override(x_186, x_187, x_188);
x_190 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_19, x_189, x_2, x_3);
lean_dec(x_2);
lean_dec(x_189);
return x_190;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_329_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(x_9, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_10, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_1, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_7 = x_4;
x_8 = x_6;
goto block_13;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_17, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_7 = x_4;
x_8 = x_6;
goto block_13;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_16);
x_21 = lean_usize_of_nat(x_17);
lean_dec(x_17);
lean_inc(x_5);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0(x_15, x_20, x_21, x_4, x_5, x_6);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_7 = x_23;
x_8 = x_24;
goto block_13;
}
else
{
lean_dec(x_5);
return x_22;
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("number of local entries: ", 25, 25);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_lengthTR(lean_box(0), x_4);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_8);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_3);
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_11, x_12);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_16);
x_17 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_14, x_15);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_23 = x_3;
} else {
 lean_dec_ref(x_3);
 x_23 = lean_box(0);
}
lean_inc(x_21);
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_24);
x_25 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_19, x_21, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_30 = x_2;
} else {
 lean_dec_ref(x_2);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_33 = x_3;
} else {
 lean_dec_ref(x_3);
 x_33 = lean_box(0);
}
lean_inc(x_31);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
x_36 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_28, x_31, x_32);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
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
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_1, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
x_5 = x_12;
x_6 = x_13;
goto block_10;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
x_5 = x_12;
x_6 = x_13;
goto block_10;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_14);
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1(x_2, x_18, x_19, x_12, x_3, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_5 = x_21;
x_6 = x_22;
goto block_10;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370____boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_370_), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_370_), 2, 0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Linter", 6, 6);
x_7 = lean_mk_string_unchecked("MissingDocs", 11, 11);
x_8 = lean_mk_string_unchecked("missingDocsExt", 14, 14);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = l_Lean_Linter_MissingDocs_builtinHandlersRef;
x_11 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370____boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370____boxed), 4, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_box(2);
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_3);
lean_ctor_set(x_15, 5, x_3);
lean_ctor_set(x_15, 6, x_2);
lean_ctor_set(x_15, 7, x_14);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*8, x_16);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_15, x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370__spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_370_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_MissingDocs_initFn___lam__3____x40_Lean_Linter_MissingDocs___hyg_370_(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_initFn___lam__4____x40_Lean_Linter_MissingDocs___hyg_370_(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Linter_MissingDocs_missingDocsExt;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_getHandlers(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_instInhabitedList(lean_box(0));
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Linter_MissingDocs_missingDocsExt;
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_8 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_4, x_5, x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Linter_MissingDocs_getHandlers(x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = l_Lean_NameMap_find_x3f(lean_box(0), x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_3, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_instInhabitedScope;
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_List_head_x21(lean_box(0), x_18, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Linter_getLinterMissingDocs(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
x_24 = lean_apply_5(x_14, x_23, x_1, x_2, x_3, x_17);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Linter_MissingDocs_getHandlers(x_27);
lean_inc(x_1);
x_29 = l_Lean_Syntax_getKind(x_1);
x_30 = l_Lean_NameMap_find_x3f(lean_box(0), x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_st_ref_get(x_3, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Command_instInhabitedScope;
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_List_head_x21(lean_box(0), x_37, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Linter_getLinterMissingDocs(x_40);
lean_dec(x_40);
x_42 = lean_box(x_41);
x_43 = lean_apply_5(x_33, x_42, x_1, x_2, x_3, x_36);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_missingDocs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_missingDocs___lam__0), 4, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Linter", 6, 6);
x_4 = lean_mk_string_unchecked("MissingDocs", 11, 11);
x_5 = lean_mk_string_unchecked("missingDocs", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_772_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_MissingDocs_missingDocs;
x_3 = l_Lean_Elab_Command_addLinter(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lean_Linter_MissingDocs_builtinHandlersRef;
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_6, x_1, x_2);
x_9 = lean_st_ref_set(x_4, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_150 = lean_box(0);
x_151 = lean_unbox(x_150);
x_152 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(x_8, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_mk_string_unchecked("invalid attribute '", 19, 19);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = l_Lean_MessageData_ofName(x_5);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("', must be global", 17, 17);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_159, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_160;
}
else
{
lean_object* x_161; 
x_161 = lean_st_ref_get(x_10, x_11);
if (x_4 == 0)
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Environment_getModuleIdxFor_x3f(x_165, x_6);
if (lean_obj_tag(x_166) == 0)
{
lean_free_object(x_161);
lean_dec(x_5);
x_111 = x_165;
x_112 = x_9;
x_113 = x_10;
x_114 = x_164;
goto block_149;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_mk_string_unchecked("invalid attribute '", 19, 19);
x_168 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
x_169 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set_tag(x_161, 7);
lean_ctor_set(x_161, 1, x_169);
lean_ctor_set(x_161, 0, x_168);
x_170 = lean_mk_string_unchecked("', declaration is in an imported module", 39, 39);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_161);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_172, x_9, x_10, x_164);
lean_dec(x_10);
lean_dec(x_9);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_161, 0);
x_175 = lean_ctor_get(x_161, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_161);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Environment_getModuleIdxFor_x3f(x_176, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_dec(x_5);
x_111 = x_176;
x_112 = x_9;
x_113 = x_10;
x_114 = x_175;
goto block_149;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_mk_string_unchecked("invalid attribute '", 19, 19);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = l_Lean_MessageData_ofName(x_5);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked("', declaration is in an imported module", 39, 39);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_184, x_9, x_10, x_175);
lean_dec(x_10);
lean_dec(x_9);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_5);
x_186 = lean_ctor_get(x_161, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_161, 1);
lean_inc(x_187);
lean_dec(x_161);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_dec(x_186);
x_111 = x_188;
x_112 = x_9;
x_113 = x_10;
x_114 = x_187;
goto block_149;
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_mk_string_unchecked("addBuiltinHandler", 17, 17);
x_19 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_15);
x_21 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_13);
x_22 = l_Lean_mkAppB(x_20, x_21, x_17);
x_23 = l_Lean_declareBuiltin(x_6, x_22, x_14, x_12, x_16);
return x_23;
}
block_94:
{
if (x_4 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_st_ref_get(x_29, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_28, 2);
lean_inc(x_36);
lean_ctor_set(x_31, 1, x_36);
lean_ctor_set(x_31, 0, x_35);
lean_inc(x_6);
x_37 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(x_6, x_31, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Linter_MissingDocs_missingDocsExt;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_40, x_27, x_42);
x_44 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_43, x_29, x_39);
lean_dec(x_29);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_28, 5);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_io_error_to_string(x_46);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_37, 0, x_51);
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_54 = lean_ctor_get(x_28, 5);
lean_inc(x_54);
lean_dec(x_28);
x_55 = lean_io_error_to_string(x_52);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_MessageData_ofFormat(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_31, 0);
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_31);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_28, 2);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_6);
x_65 = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(x_6, x_64, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_28);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Linter_MissingDocs_missingDocsExt;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_25);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_68, x_27, x_70);
x_72 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_71, x_29, x_67);
lean_dec(x_29);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_6);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_28, 5);
lean_inc(x_76);
lean_dec(x_28);
x_77 = lean_io_error_to_string(x_73);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_27);
x_82 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
x_83 = lean_mk_string_unchecked("SimpleHandler", 13, 13);
lean_inc(x_83);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_const___override(x_84, x_85);
x_87 = lean_expr_eqv(x_82, x_86);
lean_dec(x_86);
lean_dec(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_83);
lean_inc(x_6);
x_88 = l_Lean_Expr_const___override(x_6, x_85);
x_12 = x_29;
x_13 = x_25;
x_14 = x_28;
x_15 = x_85;
x_16 = x_30;
x_17 = x_88;
goto block_24;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_mk_string_unchecked("toHandler", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_83, x_89);
x_91 = l_Lean_Expr_const___override(x_90, x_85);
lean_inc(x_6);
x_92 = l_Lean_Expr_const___override(x_6, x_85);
x_93 = l_Lean_Expr_app___override(x_91, x_92);
x_12 = x_29;
x_13 = x_25;
x_14 = x_28;
x_15 = x_85;
x_16 = x_30;
x_17 = x_93;
goto block_24;
}
}
}
block_110:
{
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_mk_string_unchecked("unexpected missing docs handler at '", 36, 36);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = l_Lean_MessageData_ofName(x_6);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_mk_string_unchecked("', `MissingDocs.Handler` or `MissingDocs.SimpleHandler` expected", 64, 64);
x_107 = l_Lean_stringToMessageData(x_106);
lean_dec(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_108, x_96, x_98, x_95);
lean_dec(x_98);
lean_dec(x_96);
return x_109;
}
else
{
x_25 = x_97;
x_26 = x_99;
x_27 = x_100;
x_28 = x_96;
x_29 = x_98;
x_30 = x_95;
goto block_94;
}
}
block_149:
{
lean_object* x_115; 
lean_inc(x_6);
x_115 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_6, x_112, x_113, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Attribute_Builtin_getIdent(x_7, x_112, x_113, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_box(0);
lean_inc(x_113);
lean_inc(x_112);
x_122 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_119, x_121, x_112, x_113, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_ConstantInfo_levelParams(x_116);
x_126 = l_List_isEmpty___redArg(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
x_95 = x_124;
x_96 = x_112;
x_97 = x_123;
x_98 = x_113;
x_99 = x_116;
x_100 = x_111;
x_101 = x_126;
goto block_110;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_127 = l_Lean_ConstantInfo_type(x_116);
x_128 = lean_mk_string_unchecked("Handler", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_129 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_128);
x_130 = lean_box(0);
x_131 = l_Lean_Expr_const___override(x_129, x_130);
x_132 = lean_expr_eqv(x_127, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_mk_string_unchecked("SimpleHandler", 13, 13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_134 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_133);
x_135 = l_Lean_Expr_const___override(x_134, x_130);
x_136 = lean_expr_eqv(x_127, x_135);
lean_dec(x_135);
lean_dec(x_127);
x_95 = x_124;
x_96 = x_112;
x_97 = x_123;
x_98 = x_113;
x_99 = x_116;
x_100 = x_111;
x_101 = x_136;
goto block_110;
}
else
{
lean_dec(x_127);
x_25 = x_123;
x_26 = x_116;
x_27 = x_111;
x_28 = x_112;
x_29 = x_113;
x_30 = x_124;
goto block_94;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_122);
if (x_137 == 0)
{
return x_122;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_122, 0);
x_139 = lean_ctor_get(x_122, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_122);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_118);
if (x_141 == 0)
{
return x_118;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_118, 0);
x_143 = lean_ctor_get(x_118, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_118);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_115);
if (x_145 == 0)
{
return x_115;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_115, 0);
x_147 = lean_ctor_get(x_115, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_115);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_33; lean_object* x_34; 
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Linter", 6, 6);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("MissingDocs", 11, 11);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
lean_inc(x_6);
x_16 = l_Lean_Name_str___override(x_15, x_6);
lean_inc(x_8);
x_17 = l_Lean_Name_str___override(x_16, x_8);
lean_inc(x_10);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(802u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_33 = lean_box(x_2);
lean_inc(x_3);
x_34 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802____boxed), 11, 5);
lean_closure_set(x_34, 0, x_6);
lean_closure_set(x_34, 1, x_8);
lean_closure_set(x_34, 2, x_10);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_3);
if (x_2 == 0)
{
lean_object* x_35; 
x_35 = lean_mk_string_unchecked("", 0, 0);
x_23 = x_34;
x_24 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = lean_mk_string_unchecked("(builtin) ", 10, 10);
x_23 = x_34;
x_24 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_mk_string_unchecked("adds a syntax traversal for the missing docs linter", 51, 51);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_29);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_1);
x_31 = l_Lean_registerBuiltinAttribute(x_30, x_4);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_802_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802____boxed), 4, 0);
x_3 = lean_box(1);
x_4 = lean_mk_string_unchecked("builtin_missing_docs_handler", 28, 28);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_unbox(x_3);
lean_inc(x_2);
x_7 = l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802_(x_2, x_6, x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_string_unchecked("missing_docs_handler", 20, 20);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unbox(x_9);
x_13 = l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802_(x_2, x_12, x_11, x_8);
return x_13;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_initFn___lam__0____x40_Lean_Linter_MissingDocs___hyg_802_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_8);
lean_dec(x_8);
x_14 = l_Lean_Linter_MissingDocs_initFn___lam__1____x40_Lean_Linter_MissingDocs___hyg_802_(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_13, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Linter_MissingDocs_initFn___lam__2____x40_Lean_Linter_MissingDocs___hyg_802_(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_7 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_MessageData_ofName(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked(" false`", 7, 7);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_mk_string_unchecked("\n", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0(x_2, x_23, x_4, x_5, x_6);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Linter_linter_missingDocs;
x_7 = lean_mk_string_unchecked("missing doc string for ", 23, 23);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = l_Lean_stringToMessageData(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0(x_6, x_1, x_13, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_logLint___at___Lean_Linter_MissingDocs_lint_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_lint(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_lintNamed___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_lintNamed___lam__0___boxed), 1, 0);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_string_append(x_2, x_7);
lean_dec(x_7);
x_9 = l_Lean_Syntax_getId(x_1);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_9, x_11, x_6);
x_13 = lean_string_append(x_8, x_12);
lean_dec(x_12);
x_14 = l_Lean_Linter_MissingDocs_lint(x_1, x_13, x_3, x_4, x_5);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_MissingDocs_lintNamed___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_lintNamed(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_lintNamed___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lean_Syntax_getId(x_1);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_7);
x_13 = l_Lean_Name_toString(x_10, x_12, x_7);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked(".", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lean_Syntax_getId(x_2);
x_18 = lean_unbox(x_11);
x_19 = l_Lean_Name_toString(x_17, x_18, x_7);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_Lean_Linter_MissingDocs_lint(x_2, x_20, x_4, x_5, x_6);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_MissingDocs_lintField(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_lintNamed___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lean_Syntax_getId(x_1);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_7);
x_13 = l_Lean_Name_toString(x_10, x_12, x_7);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked(".", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lean_Syntax_getId(x_2);
x_18 = lean_unbox(x_11);
x_19 = l_Lean_Name_toString(x_17, x_18, x_7);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_Lean_Linter_MissingDocs_lint(x_2, x_20, x_4, x_5, x_6);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_MissingDocs_lintStructField(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_box(1);
x_6 = lean_unsigned_to_nat(1u);
x_13 = lean_array_uget(x_1, x_2);
x_14 = l_Lean_Syntax_getArg(x_13, x_6);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Attr", 4, 4);
x_18 = lean_mk_string_unchecked("simple", 6, 6);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_14);
x_20 = l_Lean_Syntax_isOfKind(x_14, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_14);
x_7 = x_20;
goto block_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_14, x_21);
lean_dec(x_14);
x_23 = l_Lean_Syntax_getId(x_22);
lean_dec(x_22);
x_24 = lean_erase_macro_scopes(x_23);
x_25 = lean_mk_string_unchecked("inherit_doc", 11, 11);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_name_eq(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_7 = x_27;
goto block_12;
}
block_12:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = lean_usize_of_nat(x_6);
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
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
return x_29;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getSepArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0(x_6, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Linter_MissingDocs_hasInheritDoc_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getKind(x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Command", 7, 7);
x_10 = lean_mk_string_unchecked("private", 7, 7);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_name_eq(x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Syntax_getArg(x_1, x_4);
x_14 = l_Lean_Syntax_isNone(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
return x_14;
}
else
{
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Command", 7, 7);
x_9 = lean_mk_string_unchecked("abbrev", 6, 6);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_name_eq(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_12);
x_14 = lean_name_eq(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_15);
x_17 = lean_name_eq(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_mk_string_unchecked("axiom", 5, 5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_18);
x_20 = lean_name_eq(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_mk_string_unchecked("inductive", 9, 9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_21);
x_23 = lean_name_eq(x_1, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_mk_string_unchecked("classInductive", 14, 14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_24);
x_26 = lean_name_eq(x_1, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_mk_string_unchecked("structure", 9, 9);
x_28 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_27);
x_29 = lean_name_eq(x_1, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_mk_string_unchecked("public structure", 16, 16);
x_33 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_32, x_3, x_4, x_5);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = lean_mk_string_unchecked("public inductive", 16, 16);
x_35 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_34, x_3, x_4, x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = lean_mk_string_unchecked("public inductive", 16, 16);
x_37 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_36, x_3, x_4, x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = lean_mk_string_unchecked("public axiom", 12, 12);
x_39 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_38, x_3, x_4, x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_mk_string_unchecked("public opaque", 13, 13);
x_41 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_40, x_3, x_4, x_5);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_mk_string_unchecked("public def", 10, 10);
x_43 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_42, x_3, x_4, x_5);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = lean_mk_string_unchecked("public abbrev", 13, 13);
x_45 = l_Lean_Linter_MissingDocs_lintNamed(x_2, x_44, x_3, x_4, x_5);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_lintDeclHead(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_instDecidableEqPos(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_uint64_of_nat(x_4);
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
x_29 = lean_uint64_of_nat(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 11)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Syntax_getRange_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_array_get_size(x_10);
x_13 = lean_uint64_of_nat(x_11);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_unsigned_to_nat(16u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_sub(x_23, x_25);
x_27 = lean_usize_land(x_22, x_26);
x_28 = lean_array_uget(x_10, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_11, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_ctor_get(x_5, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_28);
x_36 = lean_array_uset(x_10, x_27, x_35);
x_37 = lean_nat_shiftl(x_34, x_2);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_36);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1___redArg(x_36);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_28);
x_46 = lean_array_uset(x_10, x_27, x_45);
x_47 = lean_nat_shiftl(x_44, x_2);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_46);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Linter_MissingDocs_checkDecl_spec__1___redArg(x_46);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_5;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArg(x_9, x_6);
lean_dec(x_9);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Command", 7, 7);
x_15 = lean_mk_string_unchecked("private", 7, 7);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_18 = lean_name_eq(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_8);
x_21 = lean_array_uget(x_2, x_3);
x_22 = l_Lean_Elab_InfoTree_foldInfo___redArg(x_20, x_5, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_22;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_11);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
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
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_13);
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_8 = lean_usize_shift_right(x_3, x_4);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_7, x_6, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = lean_unsigned_to_nat(5u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_sub(x_4, x_17);
x_19 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4(x_1, x_10, x_15, x_18, x_5);
lean_dec(x_10);
x_20 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_21 = lean_array_get_size(x_6);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_19;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_19;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4(x_1, x_6, x_24, x_25, x_19);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_usize_to_nat(x_3);
x_29 = lean_array_get_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_5;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_29, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_5;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_27, x_32, x_33, x_5);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_le(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_usize_of_nat(x_4);
x_11 = lean_ctor_get_usize(x_2, 4);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4(x_1, x_9, x_10, x_11, x_3);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_12;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_12;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_5);
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_13, x_17, x_18, x_12);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_sub(x_4, x_7);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
return x_3;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
return x_3;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_20, x_25, x_26, x_3);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4(x_1, x_28, x_3);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_5, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
return x_29;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
return x_29;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_5);
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_30, x_34, x_35, x_29);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getArg(x_15, x_12);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Command", 7, 7);
x_20 = lean_mk_string_unchecked("private", 7, 7);
x_21 = lean_usize_dec_lt(x_5, x_4);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_42; 
lean_dec(x_6);
x_23 = l_Lean_Syntax_getArg(x_11, x_10);
lean_dec(x_11);
x_24 = l_Lean_Syntax_getKind(x_16);
x_25 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_26 = lean_box(0);
x_32 = l_Lean_Syntax_getArg(x_23, x_12);
lean_dec(x_23);
x_33 = lean_name_eq(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_34 = lean_array_uget(x_3, x_5);
x_42 = l_Lean_Syntax_getRange_x3f(x_34, x_33);
if (lean_obj_tag(x_42) == 0)
{
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
goto block_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_array_get_size(x_44);
x_47 = lean_uint64_of_nat(x_45);
x_48 = lean_unsigned_to_nat(32u);
x_49 = lean_uint64_of_nat(x_48);
x_50 = lean_uint64_shift_right(x_47, x_49);
x_51 = lean_uint64_xor(x_47, x_50);
x_52 = lean_unsigned_to_nat(16u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_58 = lean_usize_of_nat(x_10);
x_59 = lean_usize_sub(x_57, x_58);
x_60 = lean_usize_land(x_56, x_59);
x_61 = lean_array_uget(x_44, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_45, x_61);
lean_dec(x_61);
lean_dec(x_45);
if (x_62 == 0)
{
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
goto block_41;
}
else
{
lean_dec(x_34);
lean_dec(x_32);
x_27 = x_9;
goto block_31;
}
}
block_31:
{
size_t x_28; size_t x_29; 
x_28 = lean_usize_of_nat(x_10);
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_6 = x_26;
x_9 = x_27;
goto _start;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_mk_string_unchecked("public field", 12, 12);
x_39 = l_Lean_Linter_MissingDocs_lintField(x_32, x_34, x_38, x_35, x_36, x_37);
lean_dec(x_34);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_27 = x_40;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_10);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getArg(x_21, x_18);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Command", 7, 7);
x_26 = lean_mk_string_unchecked("private", 7, 7);
x_27 = lean_usize_dec_lt(x_5, x_4);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_43; 
lean_dec(x_6);
x_29 = l_Lean_Syntax_getArg(x_17, x_10);
lean_dec(x_17);
x_30 = l_Lean_Syntax_getKind(x_22);
x_31 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_26);
x_32 = l_Lean_Syntax_getArg(x_29, x_18);
lean_dec(x_29);
x_33 = lean_name_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = lean_array_uget(x_3, x_5);
x_43 = l_Lean_Syntax_getRange_x3f(x_35, x_33);
if (lean_obj_tag(x_43) == 0)
{
lean_inc(x_7);
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
goto block_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; lean_object* x_62; uint8_t x_63; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_45);
x_48 = lean_uint64_of_nat(x_46);
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
x_59 = lean_usize_of_nat(x_10);
x_60 = lean_usize_sub(x_58, x_59);
x_61 = lean_usize_land(x_57, x_60);
x_62 = lean_array_uget(x_45, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_46, x_62);
lean_dec(x_62);
lean_dec(x_46);
if (x_63 == 0)
{
lean_inc(x_7);
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
goto block_42;
}
else
{
lean_dec(x_35);
lean_dec(x_32);
x_11 = x_34;
x_12 = x_9;
goto block_16;
}
}
block_42:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_mk_string_unchecked("public field", 12, 12);
x_40 = l_Lean_Linter_MissingDocs_lintField(x_32, x_35, x_39, x_36, x_37, x_38);
lean_dec(x_35);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_11 = x_34;
x_12 = x_41;
goto block_16;
}
}
block_16:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_10);
x_14 = lean_usize_add(x_5, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9(x_1, x_2, x_3, x_4, x_14, x_11, x_7, x_8, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArg(x_1, x_10);
x_15 = l_Lean_Syntax_getArg(x_14, x_11);
lean_dec(x_14);
x_16 = l_Lean_Syntax_getArg(x_15, x_10);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("private", 7, 7);
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
x_20 = lean_box(0);
x_26 = lean_array_uget(x_3, x_5);
x_27 = l_Lean_Syntax_getArg(x_26, x_10);
x_28 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_21 = x_9;
goto block_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Command", 7, 7);
lean_inc(x_26);
x_32 = l_Lean_Syntax_getKind(x_26);
x_33 = lean_mk_string_unchecked("structSimpleBinder", 18, 18);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_34 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_33);
x_35 = lean_name_eq(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_36 = l_Lean_Syntax_getArg(x_26, x_11);
lean_dec(x_26);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = lean_array_size(x_37);
x_39 = lean_usize_of_nat(x_10);
lean_inc(x_7);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9(x_1, x_2, x_37, x_38, x_39, x_20, x_7, x_8, x_9);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_21 = x_41;
goto block_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_55; 
x_42 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_43 = l_Lean_Syntax_getKind(x_16);
x_44 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_17);
x_45 = l_Lean_Syntax_getArg(x_42, x_10);
lean_dec(x_42);
x_46 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_47 = l_Lean_Syntax_getArg(x_26, x_12);
lean_dec(x_26);
x_55 = l_Lean_Syntax_getRange_x3f(x_47, x_46);
if (lean_obj_tag(x_55) == 0)
{
lean_inc(x_7);
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_57);
x_60 = lean_uint64_of_nat(x_58);
x_61 = lean_unsigned_to_nat(32u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = lean_usize_of_nat(x_12);
x_72 = lean_usize_sub(x_70, x_71);
x_73 = lean_usize_land(x_69, x_72);
x_74 = lean_array_uget(x_57, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_58, x_74);
lean_dec(x_74);
lean_dec(x_58);
if (x_75 == 0)
{
lean_inc(x_7);
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
goto block_54;
}
else
{
lean_dec(x_47);
lean_dec(x_45);
x_21 = x_9;
goto block_25;
}
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_mk_string_unchecked("public field", 12, 12);
x_52 = l_Lean_Linter_MissingDocs_lintField(x_45, x_47, x_51, x_48, x_49, x_50);
lean_dec(x_47);
lean_dec(x_45);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_21 = x_53;
goto block_25;
}
}
}
block_25:
{
size_t x_22; size_t x_23; 
x_22 = lean_usize_of_nat(x_12);
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_20;
x_9 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArg(x_1, x_10);
x_15 = l_Lean_Syntax_getArg(x_14, x_11);
lean_dec(x_14);
x_16 = l_Lean_Syntax_getArg(x_15, x_10);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("private", 7, 7);
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
x_20 = lean_box(0);
x_26 = lean_array_uget(x_3, x_5);
x_27 = l_Lean_Syntax_getArg(x_26, x_10);
x_28 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_21 = x_9;
goto block_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Command", 7, 7);
lean_inc(x_26);
x_32 = l_Lean_Syntax_getKind(x_26);
x_33 = lean_mk_string_unchecked("structSimpleBinder", 18, 18);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_34 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_33);
x_35 = lean_name_eq(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_36 = l_Lean_Syntax_getArg(x_26, x_11);
lean_dec(x_26);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = lean_array_size(x_37);
x_39 = lean_usize_of_nat(x_10);
lean_inc(x_7);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9(x_1, x_2, x_37, x_38, x_39, x_20, x_7, x_8, x_9);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_21 = x_41;
goto block_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_55; 
x_42 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_43 = l_Lean_Syntax_getKind(x_16);
x_44 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_17);
x_45 = l_Lean_Syntax_getArg(x_42, x_10);
lean_dec(x_42);
x_46 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_47 = l_Lean_Syntax_getArg(x_26, x_12);
lean_dec(x_26);
x_55 = l_Lean_Syntax_getRange_x3f(x_47, x_46);
if (lean_obj_tag(x_55) == 0)
{
lean_inc(x_7);
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_57);
x_60 = lean_uint64_of_nat(x_58);
x_61 = lean_unsigned_to_nat(32u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = lean_usize_of_nat(x_12);
x_72 = lean_usize_sub(x_70, x_71);
x_73 = lean_usize_land(x_69, x_72);
x_74 = lean_array_uget(x_57, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_58, x_74);
lean_dec(x_74);
lean_dec(x_58);
if (x_75 == 0)
{
lean_inc(x_7);
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
goto block_54;
}
else
{
lean_dec(x_47);
lean_dec(x_45);
x_21 = x_9;
goto block_25;
}
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_mk_string_unchecked("public field", 12, 12);
x_52 = l_Lean_Linter_MissingDocs_lintField(x_45, x_47, x_51, x_48, x_49, x_50);
lean_dec(x_47);
lean_dec(x_45);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_21 = x_53;
goto block_25;
}
}
}
block_25:
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_12);
x_23 = lean_usize_add(x_5, x_22);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11(x_1, x_2, x_3, x_4, x_23, x_20, x_7, x_8, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_30; uint8_t x_31; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_12);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uget(x_2, x_4);
x_30 = l_Lean_Syntax_getArg(x_20, x_19);
x_31 = l_Lean_Syntax_isNone(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
x_21 = x_31;
goto block_29;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_20, x_32);
x_34 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_33);
lean_dec(x_33);
x_21 = x_34;
goto block_29;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = lean_usize_of_nat(x_12);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_11;
x_8 = x_13;
goto _start;
}
block_29:
{
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
x_13 = x_8;
goto block_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_Lean_Syntax_getArg(x_18, x_12);
lean_dec(x_18);
x_23 = l_Lean_Syntax_getArg(x_22, x_19);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_20, x_24);
lean_dec(x_20);
x_26 = lean_mk_string_unchecked("public constructor", 18, 18);
lean_inc(x_6);
x_27 = l_Lean_Linter_MissingDocs_lintField(x_23, x_25, x_26, x_6, x_7, x_8);
lean_dec(x_25);
lean_dec(x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_13 = x_28;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_19 = lean_array_uget(x_2, x_4);
x_20 = l_Lean_Syntax_getArg(x_19, x_11);
x_21 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec(x_19);
x_14 = x_8;
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_Lean_Syntax_getArg(x_1, x_13);
x_23 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_22);
x_24 = l_Lean_Syntax_getArg(x_23, x_11);
lean_dec(x_23);
x_25 = l_Lean_Syntax_getArg(x_19, x_13);
lean_dec(x_19);
x_26 = lean_mk_string_unchecked("computed field", 14, 14);
lean_inc(x_6);
x_27 = l_Lean_Linter_MissingDocs_lintField(x_24, x_25, x_26, x_6, x_7, x_8);
lean_dec(x_25);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_14 = x_28;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = lean_usize_of_nat(x_13);
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_12;
x_8 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = l_Lean_Syntax_getArg(x_8, x_5);
lean_dec(x_8);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Command", 7, 7);
x_14 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_name_eq(x_10, x_15);
lean_dec(x_15);
lean_dec(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_127; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_inc(x_18);
x_19 = l_Lean_Syntax_getKind(x_18);
x_127 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_6);
lean_dec(x_6);
if (x_127 == 0)
{
x_117 = x_2;
x_118 = x_3;
x_119 = x_4;
goto block_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = l_Lean_Syntax_getArg(x_18, x_17);
x_129 = l_Lean_Syntax_getArg(x_128, x_5);
lean_dec(x_128);
lean_inc(x_2);
x_130 = l_Lean_Linter_MissingDocs_lintDeclHead(x_19, x_129, x_2, x_3, x_4);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_117 = x_2;
x_118 = x_3;
x_119 = x_131;
goto block_126;
}
block_116:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_mk_string_unchecked("structure", 9, 9);
x_25 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_24);
x_26 = lean_name_eq(x_19, x_25);
lean_dec(x_25);
lean_dec(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(5u);
x_30 = l_Lean_Syntax_getArg(x_18, x_29);
lean_dec(x_18);
x_31 = l_Lean_Syntax_getArg(x_30, x_7);
lean_dec(x_30);
x_32 = l_Lean_Syntax_isNone(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_st_ref_get(x_21, x_20);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 6);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(8u);
x_40 = lean_nat_shiftl(x_39, x_7);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = l_Nat_nextPowerOfTwo(x_42);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_mk_array(x_43, x_44);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_5);
x_46 = l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4(x_1, x_38, x_33, x_5);
lean_dec(x_38);
x_47 = l_Lean_Syntax_getArg(x_31, x_5);
lean_dec(x_31);
x_48 = l_Lean_Syntax_getArgs(x_47);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_array_size(x_48);
x_51 = lean_usize_of_nat(x_5);
x_52 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11(x_1, x_46, x_48, x_50, x_51, x_49, x_22, x_21, x_36);
lean_dec(x_48);
lean_dec(x_46);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_49);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
x_59 = lean_ctor_get(x_57, 6);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_unsigned_to_nat(8u);
x_62 = lean_nat_shiftl(x_61, x_7);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = l_Nat_nextPowerOfTwo(x_64);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = lean_mk_array(x_65, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4(x_1, x_60, x_68, x_5);
lean_dec(x_60);
x_70 = l_Lean_Syntax_getArg(x_31, x_5);
lean_dec(x_31);
x_71 = l_Lean_Syntax_getArgs(x_70);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = lean_array_size(x_71);
x_74 = lean_usize_of_nat(x_5);
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11(x_1, x_69, x_71, x_73, x_74, x_72, x_22, x_21, x_58);
lean_dec(x_71);
lean_dec(x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_31);
lean_dec(x_22);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_20);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_81 = lean_unsigned_to_nat(4u);
x_82 = l_Lean_Syntax_getArg(x_18, x_81);
x_83 = l_Lean_Syntax_getArgs(x_82);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = lean_array_size(x_83);
x_86 = lean_usize_of_nat(x_5);
lean_inc(x_22);
x_87 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13(x_1, x_83, x_85, x_86, x_84, x_22, x_21, x_20);
lean_dec(x_83);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_87, 1);
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = lean_unsigned_to_nat(5u);
x_92 = l_Lean_Syntax_getArg(x_18, x_91);
lean_dec(x_18);
x_93 = l_Lean_Syntax_isNone(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; lean_object* x_98; uint8_t x_99; 
lean_free_object(x_87);
x_94 = l_Lean_Syntax_getArg(x_92, x_5);
lean_dec(x_92);
x_95 = l_Lean_Syntax_getArg(x_94, x_17);
lean_dec(x_94);
x_96 = l_Lean_Syntax_getArgs(x_95);
lean_dec(x_95);
x_97 = lean_array_size(x_96);
x_98 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14(x_1, x_96, x_97, x_86, x_84, x_22, x_21, x_89);
lean_dec(x_96);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_84);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_84);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
lean_dec(x_92);
lean_dec(x_22);
lean_ctor_set(x_87, 0, x_84);
return x_87;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_dec(x_87);
x_104 = lean_unsigned_to_nat(5u);
x_105 = l_Lean_Syntax_getArg(x_18, x_104);
lean_dec(x_18);
x_106 = l_Lean_Syntax_isNone(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = l_Lean_Syntax_getArg(x_105, x_5);
lean_dec(x_105);
x_108 = l_Lean_Syntax_getArg(x_107, x_17);
lean_dec(x_107);
x_109 = l_Lean_Syntax_getArgs(x_108);
lean_dec(x_108);
x_110 = lean_array_size(x_109);
x_111 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14(x_1, x_109, x_110, x_86, x_84, x_22, x_21, x_103);
lean_dec(x_109);
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
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_84);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_105);
lean_dec(x_22);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_84);
lean_ctor_set(x_115, 1, x_103);
return x_115;
}
}
}
}
block_126:
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_mk_string_unchecked("inductive", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_121 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_120);
x_122 = lean_name_eq(x_19, x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_mk_string_unchecked("classInductive", 14, 14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_124 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_123);
x_125 = lean_name_eq(x_19, x_124);
lean_dec(x_124);
x_20 = x_119;
x_21 = x_118;
x_22 = x_117;
x_23 = x_125;
goto block_116;
}
else
{
x_20 = x_119;
x_21 = x_118;
x_22 = x_117;
x_23 = x_122;
goto block_116;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_2);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_4);
return x_133;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Linter_MissingDocs_checkDecl_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___lam__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4_spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4_spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_foldlM___at___Lean_Linter_MissingDocs_checkDecl_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9_spec__9(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__9(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11_spec__11(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__11(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__13(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Linter_MissingDocs_checkDecl_spec__14(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("declaration", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkDecl___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_11);
lean_dec(x_9);
x_15 = lean_mk_string_unchecked("initializer", 11, 11);
x_16 = l_Lean_Linter_MissingDocs_lintNamed(x_14, x_15, x_2, x_3, x_4);
lean_dec(x_14);
return x_16;
}
}
else
{
lean_dec(x_9);
lean_dec(x_2);
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkInit(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("initialize", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkInit___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_26; uint8_t x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_8);
x_27 = l_Lean_Syntax_isNone(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Syntax_getArg(x_29, x_8);
lean_dec(x_29);
x_31 = l_Lean_Syntax_getArg(x_30, x_8);
lean_dec(x_30);
x_32 = l_Lean_Syntax_getKind(x_31);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Term", 4, 4);
x_36 = lean_mk_string_unchecked("local", 5, 5);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_name_eq(x_32, x_37);
lean_dec(x_37);
lean_dec(x_32);
if (x_38 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_25:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("notation", 8, 8);
x_20 = l_Lean_Linter_MissingDocs_lintNamed(x_18, x_19, x_2, x_3, x_4);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_mk_string_unchecked("notation", 8, 8);
x_24 = l_Lean_Linter_MissingDocs_lint(x_22, x_23, x_2, x_3, x_4);
lean_dec(x_23);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_dec(x_2);
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkNotation(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("notation", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkNotation___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_29; uint8_t x_30; 
x_8 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_1, x_8);
x_30 = l_Lean_Syntax_isNone(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
x_9 = x_30;
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = l_Lean_Syntax_getArg(x_32, x_8);
lean_dec(x_32);
x_34 = l_Lean_Syntax_getArg(x_33, x_8);
lean_dec(x_33);
x_35 = l_Lean_Syntax_getKind(x_34);
x_36 = lean_mk_string_unchecked("Lean", 4, 4);
x_37 = lean_mk_string_unchecked("Parser", 6, 6);
x_38 = lean_mk_string_unchecked("Term", 4, 4);
x_39 = lean_mk_string_unchecked("local", 5, 5);
x_40 = l_Lean_Name_mkStr4(x_36, x_37, x_38, x_39);
x_41 = lean_name_eq(x_35, x_40);
lean_dec(x_40);
lean_dec(x_35);
if (x_41 == 0)
{
x_9 = x_30;
goto block_28;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_28:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_Syntax_getArg(x_1, x_17);
x_20 = l_Lean_Syntax_getArg(x_19, x_8);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getAtomVal(x_20);
lean_dec(x_20);
x_22 = l_Lean_Linter_MissingDocs_lintNamed(x_18, x_21, x_2, x_3, x_4);
lean_dec(x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_getArg(x_24, x_8);
x_26 = l_Lean_Syntax_getAtomVal(x_25);
lean_dec(x_25);
x_27 = l_Lean_Linter_MissingDocs_lint(x_24, x_26, x_2, x_3, x_4);
lean_dec(x_26);
lean_dec(x_24);
return x_27;
}
}
else
{
lean_dec(x_2);
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkMixfix(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("mixfix", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMixfix___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_26; uint8_t x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_8);
x_27 = l_Lean_Syntax_isNone(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Syntax_getArg(x_29, x_8);
lean_dec(x_29);
x_31 = l_Lean_Syntax_getArg(x_30, x_8);
lean_dec(x_30);
x_32 = l_Lean_Syntax_getKind(x_31);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Term", 4, 4);
x_36 = lean_mk_string_unchecked("local", 5, 5);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_name_eq(x_32, x_37);
lean_dec(x_37);
lean_dec(x_32);
if (x_38 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_25:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("syntax", 6, 6);
x_20 = l_Lean_Linter_MissingDocs_lintNamed(x_18, x_19, x_2, x_3, x_4);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_mk_string_unchecked("syntax", 6, 6);
x_24 = l_Lean_Linter_MissingDocs_lint(x_22, x_23, x_2, x_3, x_4);
lean_dec(x_23);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_dec(x_2);
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkSyntax(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("syntax", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntax___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = l_Lean_Linter_MissingDocs_lintNamed(x_12, x_1, x_3, x_4, x_5);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("syntax", 6, 6);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("syntaxAbbrev", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("syntax category", 15, 15);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkSyntaxCat(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("syntaxCat", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_26; uint8_t x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_8);
x_27 = l_Lean_Syntax_isNone(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Syntax_getArg(x_29, x_8);
lean_dec(x_29);
x_31 = l_Lean_Syntax_getArg(x_30, x_8);
lean_dec(x_30);
x_32 = l_Lean_Syntax_getKind(x_31);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Term", 4, 4);
x_36 = lean_mk_string_unchecked("local", 5, 5);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_name_eq(x_32, x_37);
lean_dec(x_37);
lean_dec(x_32);
if (x_38 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_25:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("macro", 5, 5);
x_20 = l_Lean_Linter_MissingDocs_lintNamed(x_18, x_19, x_2, x_3, x_4);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_mk_string_unchecked("macro", 5, 5);
x_24 = l_Lean_Linter_MissingDocs_lint(x_22, x_23, x_2, x_3, x_4);
lean_dec(x_23);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_dec(x_2);
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkMacro(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("macro", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMacro___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_26; uint8_t x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_8);
x_27 = l_Lean_Syntax_isNone(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Syntax_getArg(x_29, x_8);
lean_dec(x_29);
x_31 = l_Lean_Syntax_getArg(x_30, x_8);
lean_dec(x_30);
x_32 = l_Lean_Syntax_getKind(x_31);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Term", 4, 4);
x_36 = lean_mk_string_unchecked("local", 5, 5);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_name_eq(x_32, x_37);
lean_dec(x_37);
lean_dec(x_32);
if (x_38 == 0)
{
x_9 = x_27;
goto block_25;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_25:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Linter_MissingDocs_hasInheritDoc(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("elab", 4, 4);
x_20 = l_Lean_Linter_MissingDocs_lintNamed(x_18, x_19, x_2, x_3, x_4);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_mk_string_unchecked("elab", 4, 4);
x_24 = l_Lean_Linter_MissingDocs_lint(x_22, x_23, x_2, x_3, x_4);
lean_dec(x_23);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_dec(x_2);
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkElab(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elab", 4, 4);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkElab___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_mk_string_unchecked("class abbrev", 12, 12);
x_13 = l_Lean_Linter_MissingDocs_lintNamed(x_11, x_12, x_2, x_3, x_4);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkClassAbbrev(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("classAbbrev", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("simp-like tactic", 16, 16);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkSimpLike(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("declareSimpLikeTactic", 21, 21);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSimpLike___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("option", 6, 6);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Option", 6, 6);
x_4 = lean_mk_string_unchecked("registerBuiltinOption", 21, 21);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_5, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("option", 6, 6);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkRegisterOption(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Option", 6, 6);
x_4 = lean_mk_string_unchecked("registerOption", 14, 14);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterOption___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_5, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("simp attr", 9, 9);
x_6 = l_Lean_Linter_MissingDocs_mkSimpleHandler(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("registerSimpAttr", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = lean_ctor_get(x_2, 5);
x_8 = lean_ctor_get(x_2, 6);
x_9 = lean_ctor_get(x_2, 7);
x_10 = lean_ctor_get(x_2, 8);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_5);
lean_ctor_set(x_12, 4, x_6);
lean_ctor_set(x_12, 5, x_7);
lean_ctor_set(x_12, 6, x_8);
lean_ctor_set(x_12, 7, x_9);
lean_ctor_set(x_12, 8, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = lean_mk_string_unchecked("set_option", 10, 10);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = lean_name_eq(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_14 = l_Lean_Linter_MissingDocs_missingDocs;
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_apply_4(x_15, x_17, x_2, x_3, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_6, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_6, x_21);
lean_dec(x_6);
lean_inc(x_2);
x_23 = l_Lean_Elab_elabSetOption___at___Lean_withSetOptionIn_spec__0(x_20, x_22, x_2, x_3, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_24);
x_27 = l_Lean_Linter_MissingDocs_missingDocs;
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_31 = lean_apply_1(x_28, x_30);
x_32 = l_Lean_Elab_Command_withScope___redArg(x_26, x_31, x_2, x_3, x_25);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_handleIn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_handleIn___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Linter_MissingDocs_handleIn(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("in", 2, 2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___boxed), 5, 0);
x_8 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = l_Lean_Linter_MissingDocs_missingDocs;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_4(x_10, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_13;
x_7 = x_14;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_box(0);
x_11 = lean_nat_dec_lt(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_8);
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0(x_7, x_15, x_16, x_10, x_2, x_3, x_4);
lean_dec(x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_MissingDocs_handleMutual___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Linter_MissingDocs_handleMutual_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_MissingDocs_handleMutual___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Linter_MissingDocs_handleMutual(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("mutual", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleMutual___boxed), 5, 0);
x_8 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_7, x_1);
return x_8;
}
}
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SetOption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SetOption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Linter_initFn____x40_Lean_Linter_MissingDocs___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_missingDocs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_missingDocs);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_329_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_MissingDocs_builtinHandlersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_MissingDocs_builtinHandlersRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_370_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_MissingDocs_missingDocsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_MissingDocs_missingDocsExt);
lean_dec_ref(res);
}l_Lean_Linter_MissingDocs_missingDocs = _init_l_Lean_Linter_MissingDocs_missingDocs();
lean_mark_persistent(l_Lean_Linter_MissingDocs_missingDocs);
if (builtin) {res = l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_772_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Linter_MissingDocs_initFn____x40_Lean_Linter_MissingDocs___hyg_802_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
