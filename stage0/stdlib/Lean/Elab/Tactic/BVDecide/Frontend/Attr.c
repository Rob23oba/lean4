// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Attr
// Imports: Lean.Util.Trace Lean.Elab.Tactic.Simp Std.Tactic.BVDecide.Syntax
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_740_(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_714_(lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Trace___hyg_1523__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_766_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_107_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_801_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_56_(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("sat", 3, 3);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
lean_inc(x_3);
x_12 = l_Lean_Name_str___override(x_11, x_3);
x_13 = lean_mk_string_unchecked("BVDecide", 8, 8);
lean_inc(x_13);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("Frontend", 8, 8);
lean_inc(x_15);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("initFn", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_@", 2, 2);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = l_Lean_Name_str___override(x_20, x_8);
x_22 = l_Lean_Name_str___override(x_21, x_10);
x_23 = l_Lean_Name_str___override(x_22, x_3);
x_24 = l_Lean_Name_str___override(x_23, x_13);
x_25 = l_Lean_Name_str___override(x_24, x_15);
x_26 = lean_mk_string_unchecked("Attr", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_mk_string_unchecked("_hyg", 4, 4);
x_29 = l_Lean_Name_str___override(x_27, x_28);
x_30 = lean_unsigned_to_nat(7u);
x_31 = l_Lean_Name_num___override(x_29, x_30);
x_32 = lean_unbox(x_6);
x_33 = l_Lean_registerTraceClass(x_5, x_32, x_31, x_1);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_56_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bv", 2, 2);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
lean_inc(x_3);
x_12 = l_Lean_Name_str___override(x_11, x_3);
x_13 = lean_mk_string_unchecked("BVDecide", 8, 8);
lean_inc(x_13);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("Frontend", 8, 8);
lean_inc(x_15);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("initFn", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_@", 2, 2);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = l_Lean_Name_str___override(x_20, x_8);
x_22 = l_Lean_Name_str___override(x_21, x_10);
x_23 = l_Lean_Name_str___override(x_22, x_3);
x_24 = l_Lean_Name_str___override(x_23, x_13);
x_25 = l_Lean_Name_str___override(x_24, x_15);
x_26 = lean_mk_string_unchecked("Attr", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_mk_string_unchecked("_hyg", 4, 4);
x_29 = l_Lean_Name_str___override(x_27, x_28);
x_30 = lean_unsigned_to_nat(56u);
x_31 = l_Lean_Name_num___override(x_29, x_30);
x_32 = lean_unbox(x_6);
x_33 = l_Lean_registerTraceClass(x_5, x_32, x_31, x_1);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_107_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("sat", 3, 3);
x_3 = lean_mk_string_unchecked("solver", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n\n     1. If this is set to something besides the empty string they will use that binary.\n\n     2. If this is set to the empty string they will check if there is a cadical binary next to theexecuting program. Usually that program is going to be `lean` itself and we do ship a`cadical` next to it.\n\n     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicatesto use the one that ships with Lean.", 499, 499);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_12 = lean_mk_string_unchecked("Frontend", 8, 8);
x_13 = l_Lean_Name_mkStr7(x_8, x_9, x_10, x_11, x_12, x_2, x_3);
x_14 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Trace___hyg_1523__spec__0(x_4, x_7, x_13, x_1);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_11 = lean_mk_string_unchecked("Frontend", 8, 8);
x_12 = lean_mk_string_unchecked("BVDecideConfig", 14, 14);
x_13 = l_Lean_Name_mkStr6(x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_13, x_1, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_37 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_38 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_37);
x_39 = l_Array_isEmpty___redArg(x_38);
x_40 = lean_box(1);
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_8, x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_7, 5);
x_46 = l_Lean_replaceRef(x_1, x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get(x_7, 2);
x_50 = lean_ctor_get(x_7, 3);
x_51 = lean_ctor_get(x_7, 4);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get(x_7, 9);
x_56 = lean_ctor_get(x_7, 10);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_58 = lean_ctor_get(x_7, 11);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_60 = lean_ctor_get(x_7, 12);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_46);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set(x_61, 12, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_59);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Elab", 4, 4);
x_65 = lean_mk_string_unchecked("Tactic", 6, 6);
x_66 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_67 = lean_mk_string_unchecked("Frontend", 8, 8);
x_68 = lean_mk_string_unchecked("BVDecideConfig", 14, 14);
x_69 = l_Lean_Name_mkStr6(x_63, x_64, x_65, x_66, x_67, x_68);
x_70 = lean_unbox(x_40);
lean_inc(x_69);
x_71 = l_Lean_Environment_contains(x_62, x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_38);
x_72 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = l_Lean_MessageData_ofName(x_69);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_74);
lean_ctor_set(x_41, 0, x_73);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_41);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_77, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_free_object(x_41);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_69, x_38, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = l_Lean_Expr_hasSyntheticSorry(x_85);
if (x_87 == 0)
{
uint8_t x_88; 
lean_free_object(x_83);
x_88 = l_Lean_Expr_hasSorry(x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_85);
x_89 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(x_85, x_5, x_6, x_61, x_8, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_dec(x_85);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = l_Lean_Exception_isInterrupt(x_90);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Exception_isRuntime(x_90);
x_10 = x_5;
x_11 = x_89;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_61;
x_16 = x_90;
x_17 = x_85;
x_18 = x_91;
x_19 = x_3;
x_20 = x_93;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_89;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_61;
x_16 = x_90;
x_17 = x_85;
x_18 = x_91;
x_19 = x_3;
x_20 = x_92;
goto block_35;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_85);
x_94 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_95, x_3, x_4, x_5, x_6, x_61, x_8, x_86);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = lean_unsigned_to_nat(10u);
x_102 = lean_unsigned_to_nat(100000u);
x_103 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 1, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 3, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 4, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 5, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 6, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 7, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 9, x_39);
lean_ctor_set(x_83, 0, x_103);
return x_83;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_83, 0);
x_105 = lean_ctor_get(x_83, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_83);
x_106 = l_Lean_Expr_hasSyntheticSorry(x_104);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasSorry(x_104);
if (x_107 == 0)
{
lean_object* x_108; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_104);
x_108 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(x_104, x_5, x_6, x_61, x_8, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
x_111 = l_Lean_Exception_isInterrupt(x_109);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Exception_isRuntime(x_109);
x_10 = x_5;
x_11 = x_108;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_61;
x_16 = x_109;
x_17 = x_104;
x_18 = x_110;
x_19 = x_3;
x_20 = x_112;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_108;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_61;
x_16 = x_109;
x_17 = x_104;
x_18 = x_110;
x_19 = x_3;
x_20 = x_111;
goto block_35;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_104);
x_113 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_114, x_3, x_4, x_5, x_6, x_61, x_8, x_105);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_unsigned_to_nat(10u);
x_121 = lean_unsigned_to_nat(100000u);
x_122 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 1, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 3, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 4, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 5, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 6, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 7, x_106);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 9, x_39);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_105);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_83);
if (x_124 == 0)
{
return x_83;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_83, 0);
x_126 = lean_ctor_get(x_83, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_83);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_128 = lean_ctor_get(x_41, 0);
x_129 = lean_ctor_get(x_41, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_41);
x_130 = lean_ctor_get(x_7, 5);
x_131 = l_Lean_replaceRef(x_1, x_130);
lean_dec(x_1);
x_132 = lean_ctor_get(x_7, 0);
x_133 = lean_ctor_get(x_7, 1);
x_134 = lean_ctor_get(x_7, 2);
x_135 = lean_ctor_get(x_7, 3);
x_136 = lean_ctor_get(x_7, 4);
x_137 = lean_ctor_get(x_7, 6);
x_138 = lean_ctor_get(x_7, 7);
x_139 = lean_ctor_get(x_7, 8);
x_140 = lean_ctor_get(x_7, 9);
x_141 = lean_ctor_get(x_7, 10);
x_142 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_143 = lean_ctor_get(x_7, 11);
x_144 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_145 = lean_ctor_get(x_7, 12);
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
x_146 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_133);
lean_ctor_set(x_146, 2, x_134);
lean_ctor_set(x_146, 3, x_135);
lean_ctor_set(x_146, 4, x_136);
lean_ctor_set(x_146, 5, x_131);
lean_ctor_set(x_146, 6, x_137);
lean_ctor_set(x_146, 7, x_138);
lean_ctor_set(x_146, 8, x_139);
lean_ctor_set(x_146, 9, x_140);
lean_ctor_set(x_146, 10, x_141);
lean_ctor_set(x_146, 11, x_143);
lean_ctor_set(x_146, 12, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*13, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*13 + 1, x_144);
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
lean_dec(x_128);
x_148 = lean_mk_string_unchecked("Lean", 4, 4);
x_149 = lean_mk_string_unchecked("Elab", 4, 4);
x_150 = lean_mk_string_unchecked("Tactic", 6, 6);
x_151 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_152 = lean_mk_string_unchecked("Frontend", 8, 8);
x_153 = lean_mk_string_unchecked("BVDecideConfig", 14, 14);
x_154 = l_Lean_Name_mkStr6(x_148, x_149, x_150, x_151, x_152, x_153);
x_155 = lean_unbox(x_40);
lean_inc(x_154);
x_156 = l_Lean_Environment_contains(x_147, x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_38);
x_157 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = l_Lean_MessageData_ofName(x_154);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_163, x_3, x_4, x_5, x_6, x_146, x_8, x_129);
lean_dec(x_8);
lean_dec(x_146);
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
lean_inc(x_8);
lean_inc(x_146);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_169 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_154, x_38, x_3, x_4, x_5, x_6, x_146, x_8, x_129);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = l_Lean_Expr_hasSyntheticSorry(x_170);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_172);
x_174 = l_Lean_Expr_hasSorry(x_170);
if (x_174 == 0)
{
lean_object* x_175; 
lean_inc(x_8);
lean_inc(x_146);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_170);
x_175 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_145_(x_170, x_5, x_6, x_146, x_8, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_dec(x_170);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
x_178 = l_Lean_Exception_isInterrupt(x_176);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = l_Lean_Exception_isRuntime(x_176);
x_10 = x_5;
x_11 = x_175;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_146;
x_16 = x_176;
x_17 = x_170;
x_18 = x_177;
x_19 = x_3;
x_20 = x_179;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_175;
x_12 = x_6;
x_13 = x_4;
x_14 = x_8;
x_15 = x_146;
x_16 = x_176;
x_17 = x_170;
x_18 = x_177;
x_19 = x_3;
x_20 = x_178;
goto block_35;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_170);
x_180 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_181 = l_Lean_stringToMessageData(x_180);
lean_dec(x_180);
x_182 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_181, x_3, x_4, x_5, x_6, x_146, x_8, x_171);
lean_dec(x_8);
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_170);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_unsigned_to_nat(10u);
x_188 = lean_unsigned_to_nat(100000u);
x_189 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*2, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 1, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 3, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 4, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 5, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 6, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 7, x_173);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 9, x_39);
if (lean_is_scalar(x_172)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_172;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_171);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = lean_ctor_get(x_169, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_169, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_193 = x_169;
} else {
 lean_dec_ref(x_169);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_195 = lean_unsigned_to_nat(10u);
x_196 = lean_box(0);
x_197 = lean_unsigned_to_nat(100000u);
x_198 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_199);
x_200 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 1, x_200);
x_201 = lean_unbox(x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 2, x_201);
x_202 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 3, x_202);
x_203 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 4, x_203);
x_204 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 5, x_204);
x_205 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 6, x_205);
x_206 = lean_unbox(x_40);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 7, x_206);
x_207 = lean_unbox(x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 8, x_207);
x_208 = lean_unbox(x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*2 + 9, x_208);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_9);
return x_209;
}
block_35:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_17);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Exception_toMessageData(x_16);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_19, x_13, x_10, x_12, x_15, x_14, x_18);
lean_dec(x_14);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_13);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_714_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("bv_normalize", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("simp theorems used by bv_normalize", 34, 34);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_9 = lean_mk_string_unchecked("Frontend", 8, 8);
x_10 = lean_mk_string_unchecked("bvNormalizeExt", 14, 14);
x_11 = l_Lean_Name_mkStr6(x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_Meta_registerSimpAttr(x_3, x_4, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_740_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("int_toBitVec", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("simp theorems used to convert UIntX/IntX statements into BitVec ones", 68, 68);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_9 = lean_mk_string_unchecked("Frontend", 8, 8);
x_10 = lean_mk_string_unchecked("intToBitVecExt", 14, 14);
x_11 = l_Lean_Name_mkStr6(x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_Meta_registerSimpAttr(x_3, x_4, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_766_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_3 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
x_5 = lean_st_mk_ref(x_4, x_1);
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
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_801_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("bv_normalize_proc", 17, 17);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("simprocs used by bv_normalize", 29, 29);
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_11 = lean_mk_string_unchecked("Frontend", 8, 8);
x_12 = lean_mk_string_unchecked("bvNormalizeSimprocExt", 21, 21);
x_13 = l_Lean_Name_mkStr6(x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = l_Lean_Meta_Simp_registerSimprocAttr(x_3, x_4, x_6, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_1, x_8);
lean_inc(x_2);
x_10 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_2);
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_mk_string_unchecked("Bool", 4, 4);
x_27 = lean_mk_string_unchecked("false", 5, 5);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = l_Lean_Expr_const___override(x_28, x_8);
x_11 = x_29;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("true", 4, 4);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = l_Lean_Expr_const___override(x_32, x_8);
x_11 = x_33;
goto block_25;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_mk_string_unchecked("declare", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Name_append(x_2, x_15);
x_17 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_16, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_13, x_10);
x_21 = lean_array_push(x_20, x_11);
x_22 = lean_array_push(x_21, x_4);
x_23 = l_Lean_mkAppN(x_9, x_22);
lean_dec(x_22);
x_24 = l_Lean_declareBuiltin(x_18, x_23, x_5, x_6, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_mk_string_unchecked("unexpected type at bv_normalize simproc", 39, 39);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = l_Lean_Syntax_getArg(x_2, x_186);
x_188 = l_Lean_Syntax_isNone(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Lean_Syntax_getArg(x_187, x_189);
lean_dec(x_187);
x_191 = l_Lean_Syntax_getKind(x_190);
x_192 = lean_mk_string_unchecked("Lean", 4, 4);
x_193 = lean_mk_string_unchecked("Parser", 6, 6);
x_194 = lean_mk_string_unchecked("Tactic", 6, 6);
x_195 = lean_mk_string_unchecked("simpPost", 8, 8);
x_196 = l_Lean_Name_mkStr4(x_192, x_193, x_194, x_195);
x_197 = lean_name_eq(x_191, x_196);
lean_dec(x_196);
lean_dec(x_191);
x_7 = x_197;
goto block_185;
}
else
{
lean_dec(x_187);
x_7 = x_188;
goto block_185;
}
block_185:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_bvar___override(x_12);
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_13, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Expr_fvar___override(x_15);
x_17 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_16, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Lean_Expr_mvar___override(x_18);
x_20 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_19, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Expr_sort___override(x_21);
x_23 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_22, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_22);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_Lean_Expr_const___override(x_26, x_25);
x_28 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_27, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_27);
return x_28;
}
case 1:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_Name_str___override(x_26, x_30);
x_32 = l_Lean_Expr_const___override(x_31, x_25);
x_33 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_32, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_32);
return x_33;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
lean_inc(x_36);
x_37 = l_Lean_Name_str___override(x_26, x_36);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
x_38 = l_Lean_Name_str___override(x_37, x_34);
x_39 = l_Lean_Expr_const___override(x_38, x_25);
x_40 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_39, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_39);
return x_40;
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_37);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
lean_inc(x_42);
x_43 = l_Lean_Name_str___override(x_26, x_42);
lean_inc(x_36);
x_44 = l_Lean_Name_str___override(x_43, x_36);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
x_45 = l_Lean_Name_str___override(x_44, x_34);
x_46 = l_Lean_Expr_const___override(x_45, x_25);
x_47 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_46, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_47;
}
case 1:
{
lean_object* x_48; 
lean_dec(x_44);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_string_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_1);
x_52 = l_Lean_Name_str___override(x_26, x_49);
x_53 = l_Lean_Name_str___override(x_52, x_42);
x_54 = l_Lean_Name_str___override(x_53, x_36);
x_55 = l_Lean_Name_str___override(x_54, x_34);
x_56 = l_Lean_Expr_const___override(x_55, x_25);
x_57 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_56, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_56);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_49);
x_58 = lean_mk_string_unchecked("Meta", 4, 4);
x_59 = lean_string_dec_eq(x_42, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_1);
x_60 = l_Lean_Name_str___override(x_26, x_50);
x_61 = l_Lean_Name_str___override(x_60, x_42);
x_62 = l_Lean_Name_str___override(x_61, x_36);
x_63 = l_Lean_Name_str___override(x_62, x_34);
x_64 = l_Lean_Expr_const___override(x_63, x_25);
x_65 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_64, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_64);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_42);
x_66 = lean_mk_string_unchecked("Simp", 4, 4);
x_67 = lean_string_dec_eq(x_36, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_3);
lean_dec(x_1);
x_68 = l_Lean_Name_str___override(x_26, x_50);
x_69 = l_Lean_Name_str___override(x_68, x_58);
x_70 = l_Lean_Name_str___override(x_69, x_36);
x_71 = l_Lean_Name_str___override(x_70, x_34);
x_72 = l_Lean_Expr_const___override(x_71, x_25);
x_73 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_72, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_72);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_36);
x_74 = lean_mk_string_unchecked("Simproc", 7, 7);
x_75 = lean_string_dec_eq(x_34, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_3);
lean_dec(x_1);
x_76 = l_Lean_Name_str___override(x_26, x_50);
x_77 = l_Lean_Name_str___override(x_76, x_58);
x_78 = l_Lean_Name_str___override(x_77, x_66);
x_79 = l_Lean_Name_str___override(x_78, x_34);
x_80 = l_Lean_Expr_const___override(x_79, x_25);
x_81 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_80, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_34);
lean_dec(x_25);
x_82 = lean_mk_string_unchecked("Sum", 3, 3);
x_83 = lean_mk_string_unchecked("inl", 3, 3);
x_84 = l_Lean_Name_mkStr2(x_82, x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Level_ofNat(x_85);
x_87 = lean_box(0);
lean_inc(x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Expr_const___override(x_84, x_89);
lean_inc(x_66);
lean_inc(x_58);
lean_inc(x_50);
x_91 = l_Lean_Name_mkStr4(x_50, x_58, x_66, x_74);
x_92 = l_Lean_Expr_const___override(x_91, x_87);
x_93 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_94 = l_Lean_Name_mkStr4(x_50, x_58, x_66, x_93);
x_95 = l_Lean_Expr_const___override(x_94, x_87);
lean_inc(x_1);
x_96 = l_Lean_Expr_const___override(x_1, x_87);
x_97 = l_Lean_mkApp3(x_90, x_92, x_95, x_96);
x_98 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0(x_3, x_1, x_7, x_97, x_4, x_5, x_10);
return x_98;
}
}
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_41, 1);
lean_inc(x_99);
lean_dec(x_41);
x_100 = lean_ctor_get(x_48, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_48, 1);
lean_inc(x_101);
lean_dec(x_48);
x_102 = l_Lean_Name_str___override(x_100, x_101);
x_103 = l_Lean_Name_str___override(x_102, x_99);
x_104 = l_Lean_Name_str___override(x_103, x_42);
x_105 = l_Lean_Name_str___override(x_104, x_36);
x_106 = l_Lean_Name_str___override(x_105, x_34);
x_107 = l_Lean_Expr_const___override(x_106, x_25);
x_108 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_107, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_107);
return x_108;
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_3);
lean_dec(x_1);
x_109 = lean_ctor_get(x_41, 1);
lean_inc(x_109);
lean_dec(x_41);
x_110 = lean_ctor_get(x_48, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_48, 1);
lean_inc(x_111);
lean_dec(x_48);
x_112 = l_Lean_Name_num___override(x_110, x_111);
x_113 = l_Lean_Name_str___override(x_112, x_109);
x_114 = l_Lean_Name_str___override(x_113, x_42);
x_115 = l_Lean_Name_str___override(x_114, x_36);
x_116 = l_Lean_Name_str___override(x_115, x_34);
x_117 = l_Lean_Expr_const___override(x_116, x_25);
x_118 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_117, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_117);
return x_118;
}
}
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_1);
x_119 = lean_ctor_get(x_41, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_41, 1);
lean_inc(x_120);
lean_dec(x_41);
x_121 = l_Lean_Name_num___override(x_119, x_120);
x_122 = l_Lean_Name_str___override(x_121, x_42);
x_123 = l_Lean_Name_str___override(x_122, x_36);
x_124 = l_Lean_Name_str___override(x_123, x_34);
x_125 = l_Lean_Expr_const___override(x_124, x_25);
x_126 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_125, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_125);
return x_126;
}
}
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_127 = lean_ctor_get(x_35, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_35, 1);
lean_inc(x_128);
lean_dec(x_35);
x_129 = l_Lean_Name_num___override(x_127, x_128);
x_130 = l_Lean_Name_str___override(x_129, x_36);
x_131 = l_Lean_Name_str___override(x_130, x_34);
x_132 = l_Lean_Expr_const___override(x_131, x_25);
x_133 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_132, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_132);
return x_133;
}
}
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_1);
x_134 = lean_ctor_get(x_24, 1);
lean_inc(x_134);
lean_dec(x_24);
x_135 = lean_ctor_get(x_29, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_29, 1);
lean_inc(x_136);
lean_dec(x_29);
x_137 = l_Lean_Name_num___override(x_135, x_136);
x_138 = l_Lean_Name_str___override(x_137, x_134);
x_139 = l_Lean_Expr_const___override(x_138, x_25);
x_140 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_139, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_139);
return x_140;
}
}
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_ctor_get(x_24, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_24, 1);
lean_inc(x_142);
lean_dec(x_24);
x_143 = l_Lean_Name_num___override(x_141, x_142);
x_144 = l_Lean_Expr_const___override(x_143, x_25);
x_145 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_144, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_144);
return x_145;
}
}
}
case 5:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_11, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_11, 1);
lean_inc(x_147);
lean_dec(x_11);
x_148 = l_Lean_Expr_app___override(x_146, x_147);
x_149 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_148, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_148);
return x_149;
}
case 6:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_ctor_get(x_11, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_11, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_11, 2);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_154 = l_Lean_Expr_lam___override(x_150, x_151, x_152, x_153);
x_155 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_154, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_154);
return x_155;
}
case 7:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_ctor_get(x_11, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_11, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_11, 2);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_160 = l_Lean_Expr_forallE___override(x_156, x_157, x_158, x_159);
x_161 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_160, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_160);
return x_161;
}
case 8:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_ctor_get(x_11, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_11, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_11, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_11, 3);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_11, sizeof(void*)*4 + 8);
lean_dec(x_11);
x_167 = l_Lean_Expr_letE___override(x_162, x_163, x_164, x_165, x_166);
x_168 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_167, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_167);
return x_168;
}
case 9:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_11, 0);
lean_inc(x_169);
lean_dec(x_11);
x_170 = l_Lean_Expr_lit___override(x_169);
x_171 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_170, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_170);
return x_171;
}
case 10:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_3);
lean_dec(x_1);
x_172 = lean_ctor_get(x_11, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_11, 1);
lean_inc(x_173);
lean_dec(x_11);
x_174 = l_Lean_Expr_mdata___override(x_172, x_173);
x_175 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_174, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_174);
return x_175;
}
default: 
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_3);
lean_dec(x_1);
x_176 = lean_ctor_get(x_11, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_11, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_11, 2);
lean_inc(x_178);
lean_dec(x_11);
x_179 = l_Lean_Expr_proj___override(x_176, x_177, x_178);
x_180 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_179, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_8);
if (x_181 == 0)
{
return x_8;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_8, 0);
x_183 = lean_ctor_get(x_8, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_8);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__0(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("Not implemented yet, [-builtin_bv_normalize_proc]", 49, 49);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_mk_string_unchecked("addBVNormalizeProcBuiltinAttr", 29, 29);
x_13 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_12);
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(x_6, x_7, x_13, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed), 4, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("BVDecide", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("Frontend", 8, 8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed), 11, 5);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_8);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_12);
lean_inc(x_12);
x_14 = l_Lean_Name_str___override(x_11, x_12);
x_15 = lean_mk_string_unchecked("initFn", 6, 6);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("_@", 2, 2);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = l_Lean_Name_str___override(x_18, x_4);
x_20 = l_Lean_Name_str___override(x_19, x_6);
x_21 = l_Lean_Name_str___override(x_20, x_8);
x_22 = l_Lean_Name_str___override(x_21, x_10);
x_23 = l_Lean_Name_str___override(x_22, x_12);
x_24 = lean_mk_string_unchecked("Attr", 4, 4);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(1213u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_mk_string_unchecked("bvNormalizeProcBuiltinAttr", 26, 26);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_mk_string_unchecked("Builtin bv_normalize simproc", 28, 28);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_35);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_13);
lean_ctor_set(x_36, 2, x_2);
x_37 = l_Lean_registerBuiltinAttribute(x_36, x_1);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_8);
lean_dec(x_8);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
lean_dec(x_7);
return x_13;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_56_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_107_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_714_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_740_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_766_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_801_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn____x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr___hyg_1213_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
