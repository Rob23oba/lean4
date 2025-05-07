// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter Lean.Parser.Module Lean.ParserCompiler Lean.Util.NumObjs Lean.Util.ShareCommon
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_pp_exprSizes;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object*);
lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_ppFnsRef;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_raw;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_MessageData_ofConst_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_Meta_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_getPPMVarsLevels(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofLazyM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_numObjs(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_mk_string_unchecked("_pp_uniq", 8, 8);
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
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_io_get_num_heartbeats(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Name_mkStr1(x_4);
x_24 = lean_uint64_of_nat(x_21);
lean_inc(x_12);
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set_usize(x_25, 4, x_7);
lean_inc(x_14);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_14);
lean_inc(x_12);
x_27 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set_usize(x_27, 4, x_7);
x_28 = lean_box(0);
x_29 = lean_box(1);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_14);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_14);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set_usize(x_32, 4, x_7);
x_33 = lean_ctor_get(x_1, 0);
lean_ctor_set(x_17, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
x_34 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set_uint64(x_34, sizeof(void*)*1, x_24);
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_26);
lean_inc(x_27);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_unbox(x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_38);
x_39 = lean_mk_empty_array_with_capacity(x_21);
lean_inc(x_35);
lean_inc(x_33);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_5);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_mk_ref(x_40, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_inheritedTraceOptions;
x_45 = lean_st_ref_get(x_44, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_42, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_119; uint8_t x_120; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_mk_string_unchecked("", 0, 0);
x_53 = l_Array_empty(lean_box(0));
x_54 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
lean_ctor_set(x_48, 1, x_53);
lean_ctor_set(x_48, 0, x_52);
x_55 = lean_ctor_get(x_1, 3);
x_56 = lean_box(0);
x_57 = lean_ctor_get(x_1, 4);
x_58 = lean_ctor_get(x_1, 5);
x_59 = l_Lean_Core_getMaxHeartbeats(x_55);
x_60 = lean_box(0);
x_61 = lean_box(0);
x_62 = l_Lean_diagnostics;
x_63 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_55, x_62);
x_119 = lean_ctor_get(x_50, 0);
lean_inc(x_119);
lean_dec(x_50);
x_120 = l_Lean_Kernel_isDiagnosticsEnabled(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
if (x_63 == 0)
{
lean_dec(x_35);
lean_inc(x_42);
x_64 = x_42;
x_65 = x_51;
goto block_103;
}
else
{
goto block_118;
}
}
else
{
if (x_63 == 0)
{
goto block_118;
}
else
{
lean_dec(x_35);
lean_inc(x_42);
x_64 = x_42;
x_65 = x_51;
goto block_103;
}
}
block_103:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_66 = l_Lean_maxRecDepth;
x_67 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_55, x_66);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_55);
x_68 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_21);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_56);
lean_ctor_set(x_68, 6, x_57);
lean_ctor_set(x_68, 7, x_58);
lean_ctor_set(x_68, 8, x_19);
lean_ctor_set(x_68, 9, x_59);
lean_ctor_set(x_68, 10, x_22);
lean_ctor_set(x_68, 11, x_60);
lean_ctor_set(x_68, 12, x_46);
lean_ctor_set_uint8(x_68, sizeof(void*)*13, x_63);
x_69 = lean_unbox(x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*13 + 1, x_69);
x_70 = lean_apply_3(x_2, x_68, x_64, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_get(x_42, x_72);
lean_dec(x_42);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_42);
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_dec(x_70);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_MessageData_toString(x_80, x_79);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_70);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_70, 0);
lean_dec(x_90);
x_91 = lean_ctor_get(x_78, 0);
lean_inc(x_91);
lean_dec(x_78);
x_92 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_93 = l___private_Init_Data_Repr_0__Nat_reprFast(x_91);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_70, 0, x_95);
return x_70;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_70, 1);
lean_inc(x_96);
lean_dec(x_70);
x_97 = lean_ctor_get(x_78, 0);
lean_inc(x_97);
lean_dec(x_78);
x_98 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_99 = l___private_Init_Data_Repr_0__Nat_reprFast(x_97);
x_100 = lean_string_append(x_98, x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
}
}
}
block_118:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_104 = lean_st_ref_take(x_42, x_51);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = l_Lean_Kernel_enableDiag(x_107, x_63);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 6);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 7);
lean_inc(x_114);
lean_dec(x_105);
x_115 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_35);
lean_ctor_set(x_115, 5, x_112);
lean_ctor_set(x_115, 6, x_113);
lean_ctor_set(x_115, 7, x_114);
x_116 = lean_st_ref_set(x_42, x_115, x_106);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_42);
x_64 = x_42;
x_65 = x_117;
goto block_103;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_182; uint8_t x_183; 
x_121 = lean_ctor_get(x_48, 0);
x_122 = lean_ctor_get(x_48, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_48);
x_123 = lean_mk_string_unchecked("", 0, 0);
x_124 = l_Array_empty(lean_box(0));
x_125 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_ctor_get(x_1, 3);
x_128 = lean_box(0);
x_129 = lean_ctor_get(x_1, 4);
x_130 = lean_ctor_get(x_1, 5);
x_131 = l_Lean_Core_getMaxHeartbeats(x_127);
x_132 = lean_box(0);
x_133 = lean_box(0);
x_134 = l_Lean_diagnostics;
x_135 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_127, x_134);
x_182 = lean_ctor_get(x_121, 0);
lean_inc(x_182);
lean_dec(x_121);
x_183 = l_Lean_Kernel_isDiagnosticsEnabled(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
if (x_135 == 0)
{
lean_dec(x_35);
lean_inc(x_42);
x_136 = x_42;
x_137 = x_122;
goto block_166;
}
else
{
goto block_181;
}
}
else
{
if (x_135 == 0)
{
goto block_181;
}
else
{
lean_dec(x_35);
lean_inc(x_42);
x_136 = x_42;
x_137 = x_122;
goto block_166;
}
}
block_166:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_138 = l_Lean_maxRecDepth;
x_139 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_127, x_138);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_127);
x_140 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_140, 0, x_125);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_140, 2, x_127);
lean_ctor_set(x_140, 3, x_21);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set(x_140, 5, x_128);
lean_ctor_set(x_140, 6, x_129);
lean_ctor_set(x_140, 7, x_130);
lean_ctor_set(x_140, 8, x_19);
lean_ctor_set(x_140, 9, x_131);
lean_ctor_set(x_140, 10, x_22);
lean_ctor_set(x_140, 11, x_132);
lean_ctor_set(x_140, 12, x_46);
lean_ctor_set_uint8(x_140, sizeof(void*)*13, x_135);
x_141 = lean_unbox(x_133);
lean_ctor_set_uint8(x_140, sizeof(void*)*13 + 1, x_141);
x_142 = lean_apply_3(x_2, x_140, x_136, x_137);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_42, x_144);
lean_dec(x_42);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_42);
x_149 = lean_ctor_get(x_142, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
lean_dec(x_142);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_MessageData_toString(x_151, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_156, 0, x_153);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_155;
 lean_ctor_set_tag(x_157, 1);
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_159 = x_142;
} else {
 lean_dec_ref(x_142);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_149, 0);
lean_inc(x_160);
lean_dec(x_149);
x_161 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_162 = l___private_Init_Data_Repr_0__Nat_reprFast(x_160);
x_163 = lean_string_append(x_161, x_162);
lean_dec(x_162);
x_164 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_164, 0, x_163);
if (lean_is_scalar(x_159)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_159;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
return x_165;
}
}
}
block_181:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_st_ref_take(x_42, x_122);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = l_Lean_Kernel_enableDiag(x_170, x_135);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 6);
lean_inc(x_176);
x_177 = lean_ctor_get(x_168, 7);
lean_inc(x_177);
lean_dec(x_168);
x_178 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 4, x_35);
lean_ctor_set(x_178, 5, x_175);
lean_ctor_set(x_178, 6, x_176);
lean_ctor_set(x_178, 7, x_177);
x_179 = lean_st_ref_set(x_42, x_178, x_169);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
lean_inc(x_42);
x_136 = x_42;
x_137 = x_180;
goto block_166;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint64_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_277; uint8_t x_278; 
x_184 = lean_ctor_get(x_17, 0);
x_185 = lean_ctor_get(x_17, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_17);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_unsigned_to_nat(1u);
x_188 = l_Lean_Name_mkStr1(x_4);
x_189 = lean_uint64_of_nat(x_186);
lean_inc(x_12);
x_190 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_190, 0, x_13);
lean_ctor_set(x_190, 1, x_12);
lean_ctor_set(x_190, 2, x_186);
lean_ctor_set(x_190, 3, x_186);
lean_ctor_set_usize(x_190, 4, x_7);
lean_inc(x_14);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_14);
lean_inc(x_12);
x_192 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_192, 0, x_15);
lean_ctor_set(x_192, 1, x_12);
lean_ctor_set(x_192, 2, x_186);
lean_ctor_set(x_192, 3, x_186);
lean_ctor_set_usize(x_192, 4, x_7);
x_193 = lean_box(0);
x_194 = lean_box(1);
lean_inc(x_14);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_14);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_14);
x_197 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_197, 0, x_16);
lean_ctor_set(x_197, 1, x_12);
lean_ctor_set(x_197, 2, x_186);
lean_ctor_set(x_197, 3, x_186);
lean_ctor_set_usize(x_197, 4, x_7);
x_198 = lean_ctor_get(x_1, 0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_187);
x_200 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set_uint64(x_200, sizeof(void*)*1, x_189);
lean_inc(x_191);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_191);
lean_inc(x_192);
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_192);
lean_ctor_set(x_202, 2, x_193);
x_203 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_203, 0, x_195);
lean_ctor_set(x_203, 1, x_196);
lean_ctor_set(x_203, 2, x_197);
x_204 = lean_unbox(x_194);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_204);
x_205 = lean_mk_empty_array_with_capacity(x_186);
lean_inc(x_201);
lean_inc(x_198);
x_206 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_206, 0, x_198);
lean_ctor_set(x_206, 1, x_5);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_200);
lean_ctor_set(x_206, 4, x_201);
lean_ctor_set(x_206, 5, x_202);
lean_ctor_set(x_206, 6, x_203);
lean_ctor_set(x_206, 7, x_205);
x_207 = lean_st_mk_ref(x_206, x_185);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_inheritedTraceOptions;
x_211 = lean_st_ref_get(x_210, x_209);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_st_ref_get(x_208, x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = lean_mk_string_unchecked("", 0, 0);
x_219 = l_Array_empty(lean_box(0));
x_220 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
if (lean_is_scalar(x_217)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_217;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
x_222 = lean_ctor_get(x_1, 3);
x_223 = lean_box(0);
x_224 = lean_ctor_get(x_1, 4);
x_225 = lean_ctor_get(x_1, 5);
x_226 = l_Lean_Core_getMaxHeartbeats(x_222);
x_227 = lean_box(0);
x_228 = lean_box(0);
x_229 = l_Lean_diagnostics;
x_230 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_222, x_229);
x_277 = lean_ctor_get(x_215, 0);
lean_inc(x_277);
lean_dec(x_215);
x_278 = l_Lean_Kernel_isDiagnosticsEnabled(x_277);
lean_dec(x_277);
if (x_278 == 0)
{
if (x_230 == 0)
{
lean_dec(x_201);
lean_inc(x_208);
x_231 = x_208;
x_232 = x_216;
goto block_261;
}
else
{
goto block_276;
}
}
else
{
if (x_230 == 0)
{
goto block_276;
}
else
{
lean_dec(x_201);
lean_inc(x_208);
x_231 = x_208;
x_232 = x_216;
goto block_261;
}
}
block_261:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_233 = l_Lean_maxRecDepth;
x_234 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_222, x_233);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_222);
x_235 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_235, 0, x_220);
lean_ctor_set(x_235, 1, x_221);
lean_ctor_set(x_235, 2, x_222);
lean_ctor_set(x_235, 3, x_186);
lean_ctor_set(x_235, 4, x_234);
lean_ctor_set(x_235, 5, x_223);
lean_ctor_set(x_235, 6, x_224);
lean_ctor_set(x_235, 7, x_225);
lean_ctor_set(x_235, 8, x_184);
lean_ctor_set(x_235, 9, x_226);
lean_ctor_set(x_235, 10, x_187);
lean_ctor_set(x_235, 11, x_227);
lean_ctor_set(x_235, 12, x_212);
lean_ctor_set_uint8(x_235, sizeof(void*)*13, x_230);
x_236 = lean_unbox(x_228);
lean_ctor_set_uint8(x_235, sizeof(void*)*13 + 1, x_236);
x_237 = lean_apply_3(x_2, x_235, x_231, x_232);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_st_ref_get(x_208, x_239);
lean_dec(x_208);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_238);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
else
{
lean_object* x_244; 
lean_dec(x_208);
x_244 = lean_ctor_get(x_237, 0);
lean_inc(x_244);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_245 = lean_ctor_get(x_237, 1);
lean_inc(x_245);
lean_dec(x_237);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_MessageData_toString(x_246, x_245);
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
x_251 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_251, 0, x_248);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_250;
 lean_ctor_set_tag(x_252, 1);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_249);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_253 = lean_ctor_get(x_237, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_254 = x_237;
} else {
 lean_dec_ref(x_237);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_244, 0);
lean_inc(x_255);
lean_dec(x_244);
x_256 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_257 = l___private_Init_Data_Repr_0__Nat_reprFast(x_255);
x_258 = lean_string_append(x_256, x_257);
lean_dec(x_257);
x_259 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_259, 0, x_258);
if (lean_is_scalar(x_254)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_254;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_253);
return x_260;
}
}
}
block_276:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_262 = lean_st_ref_take(x_208, x_216);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = l_Lean_Kernel_enableDiag(x_265, x_230);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_263, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_263, 5);
lean_inc(x_270);
x_271 = lean_ctor_get(x_263, 6);
lean_inc(x_271);
x_272 = lean_ctor_get(x_263, 7);
lean_inc(x_272);
lean_dec(x_263);
x_273 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_273, 0, x_266);
lean_ctor_set(x_273, 1, x_267);
lean_ctor_set(x_273, 2, x_268);
lean_ctor_set(x_273, 3, x_269);
lean_ctor_set(x_273, 4, x_201);
lean_ctor_set(x_273, 5, x_270);
lean_ctor_set(x_273, 6, x_271);
lean_ctor_set(x_273, 7, x_272);
x_274 = lean_st_ref_set(x_208, x_273, x_264);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
lean_inc(x_208);
x_231 = x_208;
x_232 = x_275;
goto block_261;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runCoreM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runCoreM___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runCoreM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_apply_5(x_2, x_3, x_8, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_4 = lean_box(0);
x_5 = lean_box(1);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_box(2);
x_9 = lean_alloc_ctor(0, 0, 18);
x_10 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 0, x_10);
x_11 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 1, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 2, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 3, x_13);
x_14 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 4, x_14);
x_15 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 5, x_15);
x_16 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 6, x_16);
x_17 = lean_unbox(x_4);
lean_ctor_set_uint8(x_9, 7, x_17);
x_18 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 8, x_18);
x_19 = lean_unbox(x_6);
lean_ctor_set_uint8(x_9, 9, x_19);
x_20 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, 10, x_20);
x_21 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 11, x_21);
x_22 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 12, x_22);
x_23 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 13, x_23);
x_24 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, 14, x_24);
x_25 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 15, x_25);
x_26 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 16, x_26);
x_27 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 17, x_27);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_9);
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_box(0);
x_34 = lean_box(0);
lean_inc(x_30);
x_35 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_31);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*7, x_28);
x_36 = lean_unbox(x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 8, x_36);
x_37 = lean_unbox(x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 9, x_37);
x_38 = lean_unbox(x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 10, x_38);
x_39 = lean_ctor_get(x_1, 1);
x_40 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_40);
lean_inc(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_40);
lean_inc(x_44);
lean_inc(x_41);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_to_nat(x_48);
x_50 = lean_nat_pow(x_46, x_49);
lean_dec(x_49);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = lean_usize_to_nat(x_51);
x_53 = lean_mk_empty_array_with_capacity(x_52);
lean_dec(x_52);
lean_inc(x_53);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_31);
lean_ctor_set(x_55, 3, x_31);
lean_ctor_set_usize(x_55, 4, x_48);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_40);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_40);
lean_inc_n(x_56, 2);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
lean_inc(x_39);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_29);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_58);
x_60 = lean_alloc_closure((void*)(l_Lean_PPContext_runMetaM___redArg___lam__0), 6, 3);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_2);
lean_closure_set(x_60, 2, x_35);
x_61 = l_Lean_PPContext_runCoreM___redArg(x_1, x_60, x_3);
return x_61;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runMetaM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runMetaM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Lean_sanitizeSyntax(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_PrettyPrinter_parenthesizeCategory(x_1, x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_formatCategory(x_1, x_12, x_3, x_4, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("term", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_ppCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint64_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_1);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set(x_18, 4, x_13);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_15);
lean_ctor_set_uint64(x_18, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*7 + 8, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*7 + 9, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*7 + 10, x_17);
x_19 = lean_apply_5(x_2, x_18, x_4, x_5, x_6, x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_ppTerm(x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppUsing___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_LocalContext_sanitizeNames(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_14, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("exprSizes", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("(pretty printer) prefix each embedded expression with its sizes in the format (size disregarding sharing/size with sharing/size with max sharing)", 145, 145);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_PrettyPrinter_pp_exprSizes;
x_7 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_9 = l_Lean_Expr_numObjs(x_1, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_sharecommon_quick(x_1);
x_14 = l_Lean_Expr_numObjs(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_mk_string_unchecked("[size ", 6, 6);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_18);
x_22 = lean_mk_string_unchecked("/", 1, 1);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("] ", 2, 2);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_14, 0, x_38);
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_mk_string_unchecked("[size ", 6, 6);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_45);
lean_ctor_set(x_9, 0, x_42);
x_46 = lean_mk_string_unchecked("/", 1, 1);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_47);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = l___private_Init_Data_Repr_0__Nat_reprFast(x_39);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("] ", 2, 2);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_2);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_40);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_sharecommon_quick(x_1);
x_67 = l_Lean_Expr_numObjs(x_66, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_mk_string_unchecked("[size ", 6, 6);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_73);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("/", 1, 1);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_inc(x_78);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Init_Data_Repr_0__Nat_reprFast(x_64);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
x_84 = l___private_Init_Data_Repr_0__Nat_reprFast(x_68);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_mk_string_unchecked("] ", 2, 2);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_2);
x_91 = lean_mk_string_unchecked("", 0, 0);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_70)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_70;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_69);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_2, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_delab(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___lam__0), 6, 0);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Lean_PrettyPrinter_ppUsing(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_9, x_4, x_10);
lean_dec(x_4);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_PrettyPrinter_delabCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
lean_inc(x_6);
x_28 = l_Lean_PrettyPrinter_ppTerm(x_12, x_6, x_7, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_29, x_6, x_30);
lean_dec(x_6);
x_15 = x_31;
goto block_27;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
x_15 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_is_scalar(x_14)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_14;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
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
if (lean_is_scalar(x_14)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_14;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Lean_LocalContext_sanitizeNames(x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_15, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Environment_find_x3f(x_11, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_mk_syntax_ident(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_sanitizeSyntax(x_16, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_PrettyPrinter_formatCategory(x_22, x_20, x_4, x_5, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(0);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_25);
lean_ctor_set(x_23, 0, x_7);
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
x_29 = lean_box(0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_7);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_7);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_mk_string_unchecked("pp", 2, 2);
x_37 = lean_mk_string_unchecked("tagAppFns", 9, 9);
x_38 = l_Lean_Name_mkStr2(x_36, x_37);
x_39 = lean_box(1);
x_40 = lean_alloc_ctor(1, 0, 1);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, 0, x_41);
x_42 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos), 11, 4);
lean_closure_set(x_43, 0, lean_box(0));
lean_closure_set(x_43, 1, x_38);
lean_closure_set(x_43, 2, x_40);
lean_closure_set(x_43, 3, x_42);
x_44 = l_Lean_ConstantInfo_levelParams(x_35);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_44, x_45);
x_47 = l_Lean_Expr_const___override(x_1, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_PrettyPrinter_ppExprWithInfos(x_47, x_48, x_43, x_2, x_3, x_4, x_5, x_10);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
lean_inc(x_1);
x_55 = l_Lean_Environment_find_x3f(x_52, x_1, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_4, 2);
lean_inc(x_56);
x_57 = lean_mk_syntax_ident(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Lean_sanitizeSyntax(x_57, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("term", 4, 4);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = l_Lean_PrettyPrinter_formatCategory(x_63, x_61, x_4, x_5, x_51);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_55, 0);
lean_inc(x_75);
lean_dec(x_55);
x_76 = lean_mk_string_unchecked("pp", 2, 2);
x_77 = lean_mk_string_unchecked("tagAppFns", 9, 9);
x_78 = l_Lean_Name_mkStr2(x_76, x_77);
x_79 = lean_box(1);
x_80 = lean_alloc_ctor(1, 0, 1);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 0, x_81);
x_82 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
x_83 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos), 11, 4);
lean_closure_set(x_83, 0, lean_box(0));
lean_closure_set(x_83, 1, x_78);
lean_closure_set(x_83, 2, x_80);
lean_closure_set(x_83, 3, x_82);
x_84 = l_Lean_ConstantInfo_levelParams(x_75);
lean_dec(x_75);
x_85 = lean_box(0);
x_86 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_84, x_85);
x_87 = l_Lean_Expr_const___override(x_1, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_PrettyPrinter_ppExprWithInfos(x_87, x_88, x_83, x_2, x_3, x_4, x_5, x_51);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 3);
x_14 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_2);
x_15 = lean_ctor_get(x_8, 5);
x_16 = lean_ctor_get(x_8, 6);
x_17 = lean_ctor_get(x_8, 7);
x_18 = lean_ctor_get(x_8, 8);
x_19 = lean_ctor_get(x_8, 9);
x_20 = lean_ctor_get(x_8, 10);
x_21 = lean_ctor_get(x_8, 11);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_8, 12);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_15);
lean_ctor_set(x_24, 6, x_16);
lean_ctor_set(x_24, 7, x_17);
lean_ctor_set(x_24, 8, x_18);
lean_ctor_set(x_24, 9, x_19);
lean_ctor_set(x_24, 10, x_20);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_3);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = l_Lean_PrettyPrinter_ppExpr(x_4, x_5, x_6, x_24, x_9, x_10);
return x_25;
}
}
LEAN_EXPORT lean_object* lean_pp_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
x_16 = lean_mk_string_unchecked("_uniq", 5, 5);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_inc(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_io_get_num_heartbeats(x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_box(1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Name_mkStr1(x_16);
x_28 = lean_uint64_of_nat(x_25);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set_usize(x_29, 4, x_10);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_7);
lean_inc(x_15);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_usize(x_31, 4, x_10);
x_32 = lean_box(0);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_7);
lean_inc(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
lean_inc(x_15);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_15);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set_usize(x_35, 4, x_10);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_27);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_28);
lean_inc(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_30);
lean_inc(x_31);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_unbox(x_24);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = lean_mk_empty_array_with_capacity(x_25);
lean_inc(x_41);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_20);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_41);
x_43 = lean_st_mk_ref(x_42, x_23);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_114 = l_Lean_inheritedTraceOptions;
x_115 = lean_st_ref_get(x_114, x_45);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_get(x_44, x_117);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint64_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_207; uint8_t x_208; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
x_122 = lean_box(1);
x_123 = lean_box(0);
x_124 = lean_box(2);
lean_inc(x_7);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_7);
lean_inc(x_7);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_7);
lean_inc(x_7);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_7);
lean_inc(x_7);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_7);
lean_inc(x_15);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_15);
lean_inc(x_7);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_7);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_7);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 0, 18);
x_134 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 0, x_134);
x_135 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 1, x_135);
x_136 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 2, x_136);
x_137 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 3, x_137);
x_138 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 4, x_138);
x_139 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 5, x_139);
x_140 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 6, x_140);
x_141 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, 7, x_141);
x_142 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 8, x_142);
x_143 = lean_unbox(x_122);
lean_ctor_set_uint8(x_133, 9, x_143);
x_144 = lean_unbox(x_123);
lean_ctor_set_uint8(x_133, 10, x_144);
x_145 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 11, x_145);
x_146 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 12, x_146);
x_147 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 13, x_147);
x_148 = lean_unbox(x_124);
lean_ctor_set_uint8(x_133, 14, x_148);
x_149 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 15, x_149);
x_150 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 16, x_150);
x_151 = lean_unbox(x_24);
lean_ctor_set_uint8(x_133, 17, x_151);
x_152 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_133);
x_153 = lean_box(0);
x_154 = lean_box(0);
lean_inc(x_128);
lean_inc(x_125);
x_155 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_155, 0, x_125);
lean_ctor_set(x_155, 1, x_126);
lean_ctor_set(x_155, 2, x_127);
lean_ctor_set(x_155, 3, x_125);
lean_ctor_set(x_155, 4, x_128);
lean_ctor_set(x_155, 5, x_128);
x_156 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_156, 0, x_129);
lean_ctor_set(x_156, 1, x_15);
lean_ctor_set(x_156, 2, x_25);
lean_ctor_set(x_156, 3, x_25);
lean_ctor_set_usize(x_156, 4, x_10);
lean_inc_n(x_130, 2);
x_157 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_157, 0, x_130);
lean_ctor_set(x_157, 1, x_130);
lean_ctor_set(x_157, 2, x_130);
lean_ctor_set(x_157, 3, x_131);
x_158 = lean_mk_string_unchecked("", 0, 0);
x_159 = l_Array_empty(lean_box(0));
x_160 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_32);
lean_ctor_set(x_160, 2, x_3);
lean_ctor_set(x_160, 3, x_41);
lean_ctor_set(x_160, 4, x_153);
lean_ctor_set(x_160, 5, x_25);
lean_ctor_set(x_160, 6, x_154);
lean_ctor_set_uint64(x_160, sizeof(void*)*7, x_152);
x_161 = lean_unbox(x_132);
lean_ctor_set_uint8(x_160, sizeof(void*)*7 + 8, x_161);
x_162 = lean_unbox(x_132);
lean_ctor_set_uint8(x_160, sizeof(void*)*7 + 9, x_162);
x_163 = lean_unbox(x_132);
lean_ctor_set_uint8(x_160, sizeof(void*)*7 + 10, x_163);
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_2);
lean_ctor_set(x_164, 1, x_155);
lean_ctor_set(x_164, 2, x_32);
lean_ctor_set(x_164, 3, x_156);
lean_ctor_set(x_164, 4, x_157);
x_165 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
lean_ctor_set(x_118, 1, x_159);
lean_ctor_set(x_118, 0, x_158);
x_166 = lean_box(0);
x_167 = lean_box(0);
x_168 = lean_box(0);
x_169 = lean_box(0);
x_170 = l_Lean_Core_getMaxHeartbeats(x_166);
x_171 = lean_box(0);
x_172 = l_Lean_diagnostics;
x_173 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_166, x_172);
x_207 = lean_ctor_get(x_120, 0);
lean_inc(x_207);
lean_dec(x_120);
x_208 = l_Lean_Kernel_isDiagnosticsEnabled(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
if (x_173 == 0)
{
lean_inc(x_44);
x_174 = x_44;
x_175 = x_121;
goto block_191;
}
else
{
goto block_206;
}
}
else
{
if (x_173 == 0)
{
goto block_206;
}
else
{
lean_inc(x_44);
x_174 = x_44;
x_175 = x_121;
goto block_191;
}
}
block_191:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_176 = lean_st_mk_ref(x_164, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_st_ref_get(x_174, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_maxRecDepth;
x_183 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_166, x_182);
x_184 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_184, 0, x_165);
lean_ctor_set(x_184, 1, x_118);
lean_ctor_set(x_184, 2, x_166);
lean_ctor_set(x_184, 3, x_25);
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 5, x_167);
lean_ctor_set(x_184, 6, x_168);
lean_ctor_set(x_184, 7, x_169);
lean_ctor_set(x_184, 8, x_22);
lean_ctor_set(x_184, 9, x_170);
lean_ctor_set(x_184, 10, x_26);
lean_ctor_set(x_184, 11, x_171);
lean_ctor_set(x_184, 12, x_116);
lean_ctor_set_uint8(x_184, sizeof(void*)*13, x_173);
x_185 = lean_unbox(x_132);
lean_ctor_set_uint8(x_184, sizeof(void*)*13 + 1, x_185);
x_186 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_172);
x_187 = lean_box(x_186);
lean_inc(x_177);
x_188 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprLegacy___lam__0___boxed), 10, 6);
lean_closure_set(x_188, 0, x_4);
lean_closure_set(x_188, 1, x_182);
lean_closure_set(x_188, 2, x_187);
lean_closure_set(x_188, 3, x_5);
lean_closure_set(x_188, 4, x_160);
lean_closure_set(x_188, 5, x_177);
x_189 = lean_ctor_get(x_180, 0);
lean_inc(x_189);
lean_dec(x_180);
x_190 = l_Lean_Kernel_isDiagnosticsEnabled(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
if (x_186 == 0)
{
lean_dec(x_37);
x_83 = x_174;
x_84 = x_184;
x_85 = x_177;
x_86 = x_181;
x_87 = x_188;
goto block_90;
}
else
{
x_91 = x_174;
x_92 = x_184;
x_93 = x_186;
x_94 = x_177;
x_95 = x_181;
x_96 = x_188;
goto block_113;
}
}
else
{
if (x_186 == 0)
{
x_91 = x_174;
x_92 = x_184;
x_93 = x_186;
x_94 = x_177;
x_95 = x_181;
x_96 = x_188;
goto block_113;
}
else
{
lean_dec(x_37);
x_83 = x_174;
x_84 = x_184;
x_85 = x_177;
x_86 = x_181;
x_87 = x_188;
goto block_90;
}
}
}
block_206:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_192 = lean_st_ref_take(x_44, x_121);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
x_196 = l_Lean_Kernel_enableDiag(x_195, x_173);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 5);
lean_inc(x_200);
x_201 = lean_ctor_get(x_193, 6);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 7);
lean_inc(x_202);
lean_dec(x_193);
lean_inc(x_37);
x_203 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_197);
lean_ctor_set(x_203, 2, x_198);
lean_ctor_set(x_203, 3, x_199);
lean_ctor_set(x_203, 4, x_37);
lean_ctor_set(x_203, 5, x_200);
lean_ctor_set(x_203, 6, x_201);
lean_ctor_set(x_203, 7, x_202);
x_204 = lean_st_ref_set(x_44, x_203, x_194);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_44);
x_174 = x_44;
x_175 = x_205;
goto block_191;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint64_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_297; uint8_t x_298; 
x_209 = lean_ctor_get(x_118, 0);
x_210 = lean_ctor_get(x_118, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_118);
x_211 = lean_box(1);
x_212 = lean_box(0);
x_213 = lean_box(2);
lean_inc(x_7);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_7);
lean_inc(x_7);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_7);
lean_inc(x_7);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_7);
lean_inc(x_7);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_7);
lean_inc(x_15);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_15);
lean_inc(x_7);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_7);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_7);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 0, 18);
x_223 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 0, x_223);
x_224 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 1, x_224);
x_225 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 2, x_225);
x_226 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 3, x_226);
x_227 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 4, x_227);
x_228 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 5, x_228);
x_229 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 6, x_229);
x_230 = lean_unbox(x_221);
lean_ctor_set_uint8(x_222, 7, x_230);
x_231 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 8, x_231);
x_232 = lean_unbox(x_211);
lean_ctor_set_uint8(x_222, 9, x_232);
x_233 = lean_unbox(x_212);
lean_ctor_set_uint8(x_222, 10, x_233);
x_234 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 11, x_234);
x_235 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 12, x_235);
x_236 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 13, x_236);
x_237 = lean_unbox(x_213);
lean_ctor_set_uint8(x_222, 14, x_237);
x_238 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 15, x_238);
x_239 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 16, x_239);
x_240 = lean_unbox(x_24);
lean_ctor_set_uint8(x_222, 17, x_240);
x_241 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_222);
x_242 = lean_box(0);
x_243 = lean_box(0);
lean_inc(x_217);
lean_inc(x_214);
x_244 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_244, 0, x_214);
lean_ctor_set(x_244, 1, x_215);
lean_ctor_set(x_244, 2, x_216);
lean_ctor_set(x_244, 3, x_214);
lean_ctor_set(x_244, 4, x_217);
lean_ctor_set(x_244, 5, x_217);
x_245 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_245, 0, x_218);
lean_ctor_set(x_245, 1, x_15);
lean_ctor_set(x_245, 2, x_25);
lean_ctor_set(x_245, 3, x_25);
lean_ctor_set_usize(x_245, 4, x_10);
lean_inc_n(x_219, 2);
x_246 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_246, 0, x_219);
lean_ctor_set(x_246, 1, x_219);
lean_ctor_set(x_246, 2, x_219);
lean_ctor_set(x_246, 3, x_220);
x_247 = lean_mk_string_unchecked("", 0, 0);
x_248 = l_Array_empty(lean_box(0));
x_249 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_249, 0, x_222);
lean_ctor_set(x_249, 1, x_32);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 3, x_41);
lean_ctor_set(x_249, 4, x_242);
lean_ctor_set(x_249, 5, x_25);
lean_ctor_set(x_249, 6, x_243);
lean_ctor_set_uint64(x_249, sizeof(void*)*7, x_241);
x_250 = lean_unbox(x_221);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 8, x_250);
x_251 = lean_unbox(x_221);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 9, x_251);
x_252 = lean_unbox(x_221);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 10, x_252);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_2);
lean_ctor_set(x_253, 1, x_244);
lean_ctor_set(x_253, 2, x_32);
lean_ctor_set(x_253, 3, x_245);
lean_ctor_set(x_253, 4, x_246);
x_254 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_247);
lean_ctor_set(x_255, 1, x_248);
x_256 = lean_box(0);
x_257 = lean_box(0);
x_258 = lean_box(0);
x_259 = lean_box(0);
x_260 = l_Lean_Core_getMaxHeartbeats(x_256);
x_261 = lean_box(0);
x_262 = l_Lean_diagnostics;
x_263 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_256, x_262);
x_297 = lean_ctor_get(x_209, 0);
lean_inc(x_297);
lean_dec(x_209);
x_298 = l_Lean_Kernel_isDiagnosticsEnabled(x_297);
lean_dec(x_297);
if (x_298 == 0)
{
if (x_263 == 0)
{
lean_inc(x_44);
x_264 = x_44;
x_265 = x_210;
goto block_281;
}
else
{
goto block_296;
}
}
else
{
if (x_263 == 0)
{
goto block_296;
}
else
{
lean_inc(x_44);
x_264 = x_44;
x_265 = x_210;
goto block_281;
}
}
block_281:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_266 = lean_st_mk_ref(x_253, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_st_ref_get(x_264, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_maxRecDepth;
x_273 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_256, x_272);
x_274 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_274, 0, x_254);
lean_ctor_set(x_274, 1, x_255);
lean_ctor_set(x_274, 2, x_256);
lean_ctor_set(x_274, 3, x_25);
lean_ctor_set(x_274, 4, x_273);
lean_ctor_set(x_274, 5, x_257);
lean_ctor_set(x_274, 6, x_258);
lean_ctor_set(x_274, 7, x_259);
lean_ctor_set(x_274, 8, x_22);
lean_ctor_set(x_274, 9, x_260);
lean_ctor_set(x_274, 10, x_26);
lean_ctor_set(x_274, 11, x_261);
lean_ctor_set(x_274, 12, x_116);
lean_ctor_set_uint8(x_274, sizeof(void*)*13, x_263);
x_275 = lean_unbox(x_221);
lean_ctor_set_uint8(x_274, sizeof(void*)*13 + 1, x_275);
x_276 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_262);
x_277 = lean_box(x_276);
lean_inc(x_267);
x_278 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprLegacy___lam__0___boxed), 10, 6);
lean_closure_set(x_278, 0, x_4);
lean_closure_set(x_278, 1, x_272);
lean_closure_set(x_278, 2, x_277);
lean_closure_set(x_278, 3, x_5);
lean_closure_set(x_278, 4, x_249);
lean_closure_set(x_278, 5, x_267);
x_279 = lean_ctor_get(x_270, 0);
lean_inc(x_279);
lean_dec(x_270);
x_280 = l_Lean_Kernel_isDiagnosticsEnabled(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
if (x_276 == 0)
{
lean_dec(x_37);
x_83 = x_264;
x_84 = x_274;
x_85 = x_267;
x_86 = x_271;
x_87 = x_278;
goto block_90;
}
else
{
x_91 = x_264;
x_92 = x_274;
x_93 = x_276;
x_94 = x_267;
x_95 = x_271;
x_96 = x_278;
goto block_113;
}
}
else
{
if (x_276 == 0)
{
x_91 = x_264;
x_92 = x_274;
x_93 = x_276;
x_94 = x_267;
x_95 = x_271;
x_96 = x_278;
goto block_113;
}
else
{
lean_dec(x_37);
x_83 = x_264;
x_84 = x_274;
x_85 = x_267;
x_86 = x_271;
x_87 = x_278;
goto block_90;
}
}
}
block_296:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_282 = lean_st_ref_take(x_44, x_210);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
x_286 = l_Lean_Kernel_enableDiag(x_285, x_263);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_283, 2);
lean_inc(x_288);
x_289 = lean_ctor_get(x_283, 3);
lean_inc(x_289);
x_290 = lean_ctor_get(x_283, 5);
lean_inc(x_290);
x_291 = lean_ctor_get(x_283, 6);
lean_inc(x_291);
x_292 = lean_ctor_get(x_283, 7);
lean_inc(x_292);
lean_dec(x_283);
lean_inc(x_37);
x_293 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_293, 0, x_286);
lean_ctor_set(x_293, 1, x_287);
lean_ctor_set(x_293, 2, x_288);
lean_ctor_set(x_293, 3, x_289);
lean_ctor_set(x_293, 4, x_37);
lean_ctor_set(x_293, 5, x_290);
lean_ctor_set(x_293, 6, x_291);
lean_ctor_set(x_293, 7, x_292);
x_294 = lean_st_ref_set(x_44, x_293, x_284);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
lean_inc(x_44);
x_264 = x_44;
x_265 = x_295;
goto block_281;
}
}
block_82:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_46, x_49);
lean_dec(x_46);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_get(x_44, x_51);
lean_dec(x_44);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_48);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_46);
lean_dec(x_44);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_dec(x_47);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_MessageData_toString(x_59, x_58);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_47);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_47, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_72 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_47, 0, x_74);
return x_47;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
lean_dec(x_57);
x_77 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_78 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
}
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_box(0);
x_89 = lean_apply_4(x_87, x_88, x_84, x_83, x_86);
x_46 = x_85;
x_47 = x_89;
goto block_82;
}
block_113:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_97 = lean_st_ref_take(x_91, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = l_Lean_Kernel_enableDiag(x_100, x_93);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 5);
lean_inc(x_105);
x_106 = lean_ctor_get(x_98, 6);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 7);
lean_inc(x_107);
lean_dec(x_98);
x_108 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_37);
lean_ctor_set(x_108, 5, x_105);
lean_ctor_set(x_108, 6, x_106);
lean_ctor_set(x_108, 7, x_107);
x_109 = lean_st_ref_set(x_91, x_108, x_99);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_box(0);
x_112 = lean_apply_4(x_96, x_111, x_92, x_91, x_110);
x_46 = x_94;
x_47 = x_112;
goto block_82;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint64_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; uint8_t x_408; uint8_t x_409; uint8_t x_410; uint8_t x_411; uint8_t x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; uint8_t x_418; uint8_t x_419; uint8_t x_420; uint64_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_477; uint8_t x_478; 
x_299 = lean_ctor_get(x_20, 0);
x_300 = lean_ctor_get(x_20, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_20);
x_301 = lean_box(1);
x_302 = lean_unsigned_to_nat(0u);
x_303 = lean_unsigned_to_nat(1u);
x_304 = l_Lean_Name_mkStr1(x_16);
x_305 = lean_uint64_of_nat(x_302);
lean_inc(x_15);
x_306 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_306, 0, x_17);
lean_ctor_set(x_306, 1, x_15);
lean_ctor_set(x_306, 2, x_302);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set_usize(x_306, 4, x_10);
lean_inc(x_7);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_7);
lean_inc(x_15);
x_308 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_308, 0, x_18);
lean_ctor_set(x_308, 1, x_15);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_302);
lean_ctor_set_usize(x_308, 4, x_10);
x_309 = lean_box(0);
lean_inc(x_7);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_7);
lean_inc(x_7);
x_311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_311, 0, x_7);
lean_inc(x_15);
x_312 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_312, 0, x_19);
lean_ctor_set(x_312, 1, x_15);
lean_ctor_set(x_312, 2, x_302);
lean_ctor_set(x_312, 3, x_302);
lean_ctor_set_usize(x_312, 4, x_10);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_304);
lean_ctor_set(x_313, 1, x_303);
x_314 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_314, 0, x_306);
lean_ctor_set_uint64(x_314, sizeof(void*)*1, x_305);
lean_inc(x_307);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_307);
lean_ctor_set(x_315, 1, x_307);
lean_inc(x_308);
x_316 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_316, 0, x_308);
lean_ctor_set(x_316, 1, x_308);
lean_ctor_set(x_316, 2, x_309);
x_317 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_317, 0, x_310);
lean_ctor_set(x_317, 1, x_311);
lean_ctor_set(x_317, 2, x_312);
x_318 = lean_unbox(x_301);
lean_ctor_set_uint8(x_317, sizeof(void*)*3, x_318);
x_319 = lean_mk_empty_array_with_capacity(x_302);
lean_inc(x_319);
lean_inc(x_315);
x_320 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_320, 0, x_1);
lean_ctor_set(x_320, 1, x_8);
lean_ctor_set(x_320, 2, x_313);
lean_ctor_set(x_320, 3, x_314);
lean_ctor_set(x_320, 4, x_315);
lean_ctor_set(x_320, 5, x_316);
lean_ctor_set(x_320, 6, x_317);
lean_ctor_set(x_320, 7, x_319);
x_321 = lean_st_mk_ref(x_320, x_300);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_383 = l_Lean_inheritedTraceOptions;
x_384 = lean_st_ref_get(x_383, x_323);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_st_ref_get(x_322, x_386);
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
x_391 = lean_box(1);
x_392 = lean_box(0);
x_393 = lean_box(2);
lean_inc(x_7);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_7);
lean_inc(x_7);
x_395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_395, 0, x_7);
lean_inc(x_7);
x_396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_396, 0, x_7);
lean_inc(x_7);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_7);
lean_inc(x_15);
x_398 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_398, 0, x_15);
lean_inc(x_7);
x_399 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_399, 0, x_7);
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_7);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(0, 0, 18);
x_403 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 0, x_403);
x_404 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 1, x_404);
x_405 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 2, x_405);
x_406 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 3, x_406);
x_407 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 4, x_407);
x_408 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 5, x_408);
x_409 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 6, x_409);
x_410 = lean_unbox(x_401);
lean_ctor_set_uint8(x_402, 7, x_410);
x_411 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 8, x_411);
x_412 = lean_unbox(x_391);
lean_ctor_set_uint8(x_402, 9, x_412);
x_413 = lean_unbox(x_392);
lean_ctor_set_uint8(x_402, 10, x_413);
x_414 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 11, x_414);
x_415 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 12, x_415);
x_416 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 13, x_416);
x_417 = lean_unbox(x_393);
lean_ctor_set_uint8(x_402, 14, x_417);
x_418 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 15, x_418);
x_419 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 16, x_419);
x_420 = lean_unbox(x_301);
lean_ctor_set_uint8(x_402, 17, x_420);
x_421 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_402);
x_422 = lean_box(0);
x_423 = lean_box(0);
lean_inc(x_397);
lean_inc(x_394);
x_424 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_424, 0, x_394);
lean_ctor_set(x_424, 1, x_395);
lean_ctor_set(x_424, 2, x_396);
lean_ctor_set(x_424, 3, x_394);
lean_ctor_set(x_424, 4, x_397);
lean_ctor_set(x_424, 5, x_397);
x_425 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_425, 0, x_398);
lean_ctor_set(x_425, 1, x_15);
lean_ctor_set(x_425, 2, x_302);
lean_ctor_set(x_425, 3, x_302);
lean_ctor_set_usize(x_425, 4, x_10);
lean_inc_n(x_399, 2);
x_426 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_426, 0, x_399);
lean_ctor_set(x_426, 1, x_399);
lean_ctor_set(x_426, 2, x_399);
lean_ctor_set(x_426, 3, x_400);
x_427 = lean_mk_string_unchecked("", 0, 0);
x_428 = l_Array_empty(lean_box(0));
x_429 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_429, 0, x_402);
lean_ctor_set(x_429, 1, x_309);
lean_ctor_set(x_429, 2, x_3);
lean_ctor_set(x_429, 3, x_319);
lean_ctor_set(x_429, 4, x_422);
lean_ctor_set(x_429, 5, x_302);
lean_ctor_set(x_429, 6, x_423);
lean_ctor_set_uint64(x_429, sizeof(void*)*7, x_421);
x_430 = lean_unbox(x_401);
lean_ctor_set_uint8(x_429, sizeof(void*)*7 + 8, x_430);
x_431 = lean_unbox(x_401);
lean_ctor_set_uint8(x_429, sizeof(void*)*7 + 9, x_431);
x_432 = lean_unbox(x_401);
lean_ctor_set_uint8(x_429, sizeof(void*)*7 + 10, x_432);
x_433 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_433, 0, x_2);
lean_ctor_set(x_433, 1, x_424);
lean_ctor_set(x_433, 2, x_309);
lean_ctor_set(x_433, 3, x_425);
lean_ctor_set(x_433, 4, x_426);
x_434 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
if (lean_is_scalar(x_390)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_390;
}
lean_ctor_set(x_435, 0, x_427);
lean_ctor_set(x_435, 1, x_428);
x_436 = lean_box(0);
x_437 = lean_box(0);
x_438 = lean_box(0);
x_439 = lean_box(0);
x_440 = l_Lean_Core_getMaxHeartbeats(x_436);
x_441 = lean_box(0);
x_442 = l_Lean_diagnostics;
x_443 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_436, x_442);
x_477 = lean_ctor_get(x_388, 0);
lean_inc(x_477);
lean_dec(x_388);
x_478 = l_Lean_Kernel_isDiagnosticsEnabled(x_477);
lean_dec(x_477);
if (x_478 == 0)
{
if (x_443 == 0)
{
lean_inc(x_322);
x_444 = x_322;
x_445 = x_389;
goto block_461;
}
else
{
goto block_476;
}
}
else
{
if (x_443 == 0)
{
goto block_476;
}
else
{
lean_inc(x_322);
x_444 = x_322;
x_445 = x_389;
goto block_461;
}
}
block_351:
{
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_st_ref_get(x_324, x_327);
lean_dec(x_324);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_st_ref_get(x_322, x_329);
lean_dec(x_322);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_326);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
else
{
lean_object* x_334; 
lean_dec(x_324);
lean_dec(x_322);
x_334 = lean_ctor_get(x_325, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_335 = lean_ctor_get(x_325, 1);
lean_inc(x_335);
lean_dec(x_325);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = l_Lean_MessageData_toString(x_336, x_335);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_341, 0, x_338);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_340;
 lean_ctor_set_tag(x_342, 1);
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_339);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_343 = lean_ctor_get(x_325, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_344 = x_325;
} else {
 lean_dec_ref(x_325);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_334, 0);
lean_inc(x_345);
lean_dec(x_334);
x_346 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_347 = l___private_Init_Data_Repr_0__Nat_reprFast(x_345);
x_348 = lean_string_append(x_346, x_347);
lean_dec(x_347);
x_349 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_349, 0, x_348);
if (lean_is_scalar(x_344)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_344;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_343);
return x_350;
}
}
}
block_359:
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_box(0);
x_358 = lean_apply_4(x_356, x_357, x_353, x_352, x_355);
x_324 = x_354;
x_325 = x_358;
goto block_351;
}
block_382:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_366 = lean_st_ref_take(x_360, x_364);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = l_Lean_Kernel_enableDiag(x_369, x_362);
x_371 = lean_ctor_get(x_367, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_367, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_367, 5);
lean_inc(x_374);
x_375 = lean_ctor_get(x_367, 6);
lean_inc(x_375);
x_376 = lean_ctor_get(x_367, 7);
lean_inc(x_376);
lean_dec(x_367);
x_377 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_377, 0, x_370);
lean_ctor_set(x_377, 1, x_371);
lean_ctor_set(x_377, 2, x_372);
lean_ctor_set(x_377, 3, x_373);
lean_ctor_set(x_377, 4, x_315);
lean_ctor_set(x_377, 5, x_374);
lean_ctor_set(x_377, 6, x_375);
lean_ctor_set(x_377, 7, x_376);
x_378 = lean_st_ref_set(x_360, x_377, x_368);
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_box(0);
x_381 = lean_apply_4(x_365, x_380, x_361, x_360, x_379);
x_324 = x_363;
x_325 = x_381;
goto block_351;
}
block_461:
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_446 = lean_st_mk_ref(x_433, x_445);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_449 = lean_st_ref_get(x_444, x_448);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = l_Lean_maxRecDepth;
x_453 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_436, x_452);
x_454 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_454, 0, x_434);
lean_ctor_set(x_454, 1, x_435);
lean_ctor_set(x_454, 2, x_436);
lean_ctor_set(x_454, 3, x_302);
lean_ctor_set(x_454, 4, x_453);
lean_ctor_set(x_454, 5, x_437);
lean_ctor_set(x_454, 6, x_438);
lean_ctor_set(x_454, 7, x_439);
lean_ctor_set(x_454, 8, x_299);
lean_ctor_set(x_454, 9, x_440);
lean_ctor_set(x_454, 10, x_303);
lean_ctor_set(x_454, 11, x_441);
lean_ctor_set(x_454, 12, x_385);
lean_ctor_set_uint8(x_454, sizeof(void*)*13, x_443);
x_455 = lean_unbox(x_401);
lean_ctor_set_uint8(x_454, sizeof(void*)*13 + 1, x_455);
x_456 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_442);
x_457 = lean_box(x_456);
lean_inc(x_447);
x_458 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprLegacy___lam__0___boxed), 10, 6);
lean_closure_set(x_458, 0, x_4);
lean_closure_set(x_458, 1, x_452);
lean_closure_set(x_458, 2, x_457);
lean_closure_set(x_458, 3, x_5);
lean_closure_set(x_458, 4, x_429);
lean_closure_set(x_458, 5, x_447);
x_459 = lean_ctor_get(x_450, 0);
lean_inc(x_459);
lean_dec(x_450);
x_460 = l_Lean_Kernel_isDiagnosticsEnabled(x_459);
lean_dec(x_459);
if (x_460 == 0)
{
if (x_456 == 0)
{
lean_dec(x_315);
x_352 = x_444;
x_353 = x_454;
x_354 = x_447;
x_355 = x_451;
x_356 = x_458;
goto block_359;
}
else
{
x_360 = x_444;
x_361 = x_454;
x_362 = x_456;
x_363 = x_447;
x_364 = x_451;
x_365 = x_458;
goto block_382;
}
}
else
{
if (x_456 == 0)
{
x_360 = x_444;
x_361 = x_454;
x_362 = x_456;
x_363 = x_447;
x_364 = x_451;
x_365 = x_458;
goto block_382;
}
else
{
lean_dec(x_315);
x_352 = x_444;
x_353 = x_454;
x_354 = x_447;
x_355 = x_451;
x_356 = x_458;
goto block_359;
}
}
}
block_476:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_462 = lean_st_ref_take(x_322, x_389);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
x_466 = l_Lean_Kernel_enableDiag(x_465, x_443);
x_467 = lean_ctor_get(x_463, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_463, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_463, 3);
lean_inc(x_469);
x_470 = lean_ctor_get(x_463, 5);
lean_inc(x_470);
x_471 = lean_ctor_get(x_463, 6);
lean_inc(x_471);
x_472 = lean_ctor_get(x_463, 7);
lean_inc(x_472);
lean_dec(x_463);
lean_inc(x_315);
x_473 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_473, 0, x_466);
lean_ctor_set(x_473, 1, x_467);
lean_ctor_set(x_473, 2, x_468);
lean_ctor_set(x_473, 3, x_469);
lean_ctor_set(x_473, 4, x_315);
lean_ctor_set(x_473, 5, x_470);
lean_ctor_set(x_473, 6, x_471);
lean_ctor_set(x_473, 7, x_472);
x_474 = lean_st_ref_set(x_322, x_473, x_464);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
lean_inc(x_322);
x_444 = x_322;
x_445 = x_475;
goto block_461;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_PrettyPrinter_ppExprLegacy___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("tactic", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_ppCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("command", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_ppCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer), 5, 0);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter), 5, 0);
x_10 = l_Lean_PrettyPrinter_format(x_9, x_7, x_2, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_ConstantInfo_levelParams(x_9);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_11, x_12);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = l_Lean_pp_raw;
x_17 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_9);
x_18 = lean_box(1);
x_19 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed), 8, 1);
lean_closure_set(x_20, 0, x_18);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_PrettyPrinter_delabCore___redArg(x_14, x_19, x_20, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = l_Lean_PrettyPrinter_ppTerm(x_25, x_4, x_5, x_23);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_22, 0, x_29);
lean_ctor_set(x_27, 0, x_22);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_22, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_22);
lean_dec(x_26);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = l_Lean_PrettyPrinter_ppTerm(x_37, x_4, x_5, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
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
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_38);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_expr_dbg_to_string(x_14);
lean_dec(x_14);
x_54 = lean_mk_string_unchecked(" : ", 3, 3);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
x_57 = lean_expr_dbg_to_string(x_56);
lean_dec(x_56);
x_58 = lean_string_append(x_55, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_64 = l_Lean_ConstantInfo_levelParams(x_62);
x_65 = lean_box(0);
x_66 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_64, x_65);
x_67 = l_Lean_Expr_const___override(x_1, x_66);
x_68 = lean_ctor_get(x_4, 2);
lean_inc(x_68);
x_69 = l_Lean_pp_raw;
x_70 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
x_71 = lean_box(1);
x_72 = lean_box(0);
x_73 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed), 8, 1);
lean_closure_set(x_73, 0, x_71);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_PrettyPrinter_delabCore___redArg(x_67, x_72, x_73, x_2, x_3, x_4, x_5, x_63);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = l_Lean_PrettyPrinter_ppTerm(x_77, x_4, x_5, x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_78);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
lean_dec(x_78);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_92 = x_74;
} else {
 lean_dec_ref(x_74);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_expr_dbg_to_string(x_67);
lean_dec(x_67);
x_95 = lean_mk_string_unchecked(" : ", 3, 3);
x_96 = lean_string_append(x_94, x_95);
lean_dec(x_95);
x_97 = l_Lean_ConstantInfo_type(x_62);
lean_dec(x_62);
x_98 = lean_expr_dbg_to_string(x_97);
lean_dec(x_97);
x_99 = lean_string_append(x_96, x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_63);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_7);
if (x_104 == 0)
{
return x_7;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_7, 0);
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_7);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_1 = x_2;
goto _start;
}
case 4:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 5:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_12);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
case 6:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_19);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_21);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
case 7:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_25);
x_28 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_26);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_29);
x_32 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_30);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 8:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 1);
x_36 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_38);
x_40 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
case 9:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; size_t x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_42);
x_45 = lean_array_size(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_usize_of_nat(x_46);
x_48 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_45, x_47, x_43);
lean_ctor_set(x_1, 2, x_48);
lean_ctor_set(x_1, 1, x_44);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_52 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_50);
x_53 = lean_array_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_usize_of_nat(x_54);
x_56 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_53, x_55, x_51);
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_56);
return x_57;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_4);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_apply_2(x_5, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_14, lean_box(0), x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_3(x_4, lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_28; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_28 = l_Lean_Exception_isInterrupt(x_8);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_8);
x_10 = x_29;
goto block_27;
}
else
{
x_10 = x_28;
goto block_27;
}
block_27:
{
if (x_10 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
lean_ctor_set(x_8, 1, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_23 = x_8;
} else {
 lean_dec_ref(x_8);
 x_23 = lean_box(0);
}
x_24 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
return x_7;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_26; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_26 = l_Lean_Exception_isInterrupt(x_6);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_6);
x_8 = x_27;
goto block_25;
}
else
{
x_8 = x_26;
goto block_25;
}
block_25:
{
if (x_8 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_13);
lean_ctor_set(x_6, 1, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_21 = x_6;
} else {
 lean_dec_ref(x_6);
 x_21 = lean_box(0);
}
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_20);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_getPPMVarsLevels(x_4);
x_6 = l_Lean_Level_format(x_2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab), 7, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos), 8, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_PPContext_runMetaM___redArg(x_1, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConstNameWithInfos), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runMetaM___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runMetaM___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runCoreM___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_7 = l_Lean_ppFnsRef;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_5);
x_9 = lean_st_ref_set(x_7, x_8, x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
lean_inc(x_2);
x_8 = l_Lean_Name_str___override(x_7, x_2);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_6);
x_14 = l_Lean_Name_str___override(x_13, x_2);
x_15 = lean_mk_string_unchecked("_hyg", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_unsigned_to_nat(1164u);
x_18 = l_Lean_Name_num___override(x_16, x_17);
x_19 = lean_unbox(x_4);
x_20 = l_Lean_registerTraceClass(x_3, x_19, x_18, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_5 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Lean_ParserCompiler_registerParserCompiler___redArg(x_6, x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("formatter", 9, 9);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_PrettyPrinter_formatterAttribute;
x_12 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Lean_ParserCompiler_registerParserCompiler___redArg(x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_mk_string_unchecked("[Error pretty printing: ", 24, 24);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_io_error_to_string(x_13);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("]", 1, 1);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_mk_string_unchecked("[Error pretty printing: ", 24, 24);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_io_error_to_string(x_23);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("]", 1, 1);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed), 1, 0);
x_4 = l_Lean_MessageData_lazy(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_ofFormatWithInfosM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofFormatWithInfosM___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_instantiateMVarsCore(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_hasSyntheticSorry(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_mk_string_unchecked("[Error pretty printing: ", 24, 24);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_io_error_to_string(x_10);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("]", 1, 1);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_mk_string_unchecked("[Error pretty printing: ", 24, 24);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_io_error_to_string(x_20);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("]", 1, 1);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofLazyM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLazyM___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLazyM___lam__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_MessageData_lazy(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_ofLazyM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofLazyM___lam__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_MessageData_ofConst_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_mk_string_unchecked("[Error pretty printing: expression not a constant]", 50, 50);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = lean_box(1);
x_6 = l_Lean_MessageData_ofFormat(x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_MessageData_ofExpr(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_panic_fn(x_13, x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isConst(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.PrettyPrinter", 18, 18);
x_4 = lean_mk_string_unchecked("Lean.MessageData.ofConst", 24, 24);
x_5 = lean_unsigned_to_nat(179u);
x_6 = lean_unsigned_to_nat(4u);
x_7 = lean_mk_string_unchecked("not a constant", 14, 14);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_MessageData_ofConst_spec__0(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_mk_string_unchecked("pp", 2, 2);
x_11 = lean_mk_string_unchecked("tagAppFns", 9, 9);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos), 11, 4);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos), 8, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
x_18 = l_Lean_MessageData_ofFormatWithInfosM(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppSignature), 6, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_PPContext_runMetaM___redArg(x_2, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
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
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_mk_string_unchecked("[Error pretty printing signature: ", 34, 34);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_io_error_to_string(x_14);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("]", 1, 1);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofName(x_1);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_32);
return x_5;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_mk_string_unchecked("[Error pretty printing signature: ", 34, 34);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_io_error_to_string(x_33);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("]", 1, 1);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(1);
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
lean_inc(x_48);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofName(x_1);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_34);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_signature___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed), 1, 0);
x_4 = l_Lean_MessageData_lazy(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_signature___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumObjs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_exprSizes = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_registerParserCompilers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
