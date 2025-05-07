// Lean compiler output
// Module: Lean.Compiler.LCNF.Types
// Imports: Lean.Compiler.BorrowedAnnotation Lean.Meta.InferType
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Level_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_term_u25fe;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object*);
lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAny(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_term_u25fe() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("term◾", 7, 5);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_mk_string_unchecked("◾", 3, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Compiler", 8, 8);
x_6 = lean_mk_string_unchecked("term◾", 7, 5);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_mk_string_unchecked("lcErased", 8, 8);
lean_inc(x_17);
x_18 = l_String_toSubstring_x27(x_17);
x_19 = l_Lean_Name_mkStr1(x_17);
lean_inc(x_19);
x_20 = l_Lean_addMacroScope(x_16, x_19, x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("ident", 5, 5);
x_5 = l_Lean_Name_mkStr1(x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Lean_replaceRef(x_1, x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
lean_dec(x_9);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Compiler", 8, 8);
x_15 = lean_mk_string_unchecked("term◾", 7, 5);
x_16 = l_Lean_Name_mkStr3(x_13, x_14, x_15);
x_17 = lean_mk_string_unchecked("◾", 3, 1);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Syntax_node1(x_12, x_16, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_erasedExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_anyExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("lcAny", 5, 5);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isErased(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("lcErased", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isAppOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isErased(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAny(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("lcAny", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isAppOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAny(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
case 7:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 2);
x_1 = x_7;
goto _start;
}
default: 
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate_rev(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_whnfD(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 3:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_3, x_16, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_Level_succ___override(x_19);
x_21 = l_Lean_Expr_sort___override(x_20);
x_22 = lean_apply_6(x_4, x_21, x_6, x_7, x_8, x_9, x_18);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lean_Level_max___override(x_24, x_25);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = lean_apply_6(x_4, x_27, x_6, x_7, x_8, x_9, x_23);
return x_28;
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Lean_Level_imax___override(x_30, x_31);
x_33 = l_Lean_Expr_sort___override(x_32);
x_34 = lean_apply_6(x_4, x_33, x_6, x_7, x_8, x_9, x_29);
return x_34;
}
case 4:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = l_Lean_Level_param___override(x_36);
x_38 = l_Lean_Expr_sort___override(x_37);
x_39 = lean_apply_6(x_4, x_38, x_6, x_7, x_8, x_9, x_35);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = l_Lean_Level_mvar___override(x_41);
x_43 = l_Lean_Expr_sort___override(x_42);
x_44 = lean_apply_6(x_4, x_43, x_6, x_7, x_8, x_9, x_40);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_dec(x_12);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_mk_empty_array_with_capacity(x_46);
x_48 = l_Lean_Compiler_LCNF_isPropFormerType_go(x_13, x_47, x_6, x_7, x_8, x_9, x_45);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_dec(x_12);
x_50 = lean_apply_6(x_4, x_13, x_6, x_7, x_8, x_9, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_push(x_1, x_3);
x_10 = l_Lean_Compiler_LCNF_isPropFormerType_go(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 6, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1___boxed), 6, 0);
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0(x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Level_succ___override(x_13);
x_15 = l_Lean_Expr_sort___override(x_14);
x_16 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Level_max___override(x_17, x_18);
x_20 = l_Lean_Expr_sort___override(x_19);
x_21 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
case 3:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lean_Level_imax___override(x_22, x_23);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_Level_param___override(x_27);
x_29 = l_Lean_Expr_sort___override(x_28);
x_30 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_29, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec(x_10);
x_32 = l_Lean_Level_mvar___override(x_31);
x_33 = l_Lean_Expr_sort___override(x_32);
x_34 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_33, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_isPropFormerType_go___lam__3), 8, 2);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_37);
x_40 = lean_expr_instantiate_rev(x_36, x_2);
lean_dec(x_2);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(x_35, x_38, x_40, x_39, x_42, x_3, x_4, x_5, x_6, x_7);
return x_43;
}
default: 
{
lean_object* x_44; 
x_44 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_8, x_9, x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_isPropFormerType_go___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = l_Lean_Compiler_LCNF_isPropFormerType_go(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_isPropFormerType(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Expr_eta(x_8);
x_11 = lean_expr_eqv(x_10, x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_dec(x_7);
x_1 = x_10;
x_6 = x_9;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_30; lean_object* x_31; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_30 = lean_is_marked_borrowed(x_1);
x_31 = lean_expr_abstract(x_13, x_2);
lean_dec(x_13);
if (x_30 == 0)
{
x_15 = x_31;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
goto block_29;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_markBorrowed(x_31);
x_15 = x_32;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
goto block_29;
}
block_29:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_push(x_2, x_6);
x_21 = l_Lean_Compiler_LCNF_toLCNFType_visitForall(x_3, x_20, x_16, x_17, x_18, x_19, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Expr_forallE___override(x_4, x_15, x_23, x_5);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_Expr_forallE___override(x_4, x_15, x_25, x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_dec(x_15);
lean_dec(x_4);
return x_21;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_9, x_2);
lean_dec(x_9);
x_13 = lean_box(x_11);
lean_inc(x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(x_8, x_11, x_12, x_14, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
x_19 = l_Lean_Compiler_LCNF_toLCNFType(x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_expr_abstract(x_21, x_2);
lean_dec(x_2);
lean_dec(x_21);
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
x_25 = lean_expr_abstract(x_23, x_2);
lean_dec(x_2);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_dec(x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_set(x_2, x_3, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = l_Lean_Compiler_LCNF_toLCNFType_visitApp(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_instantiate1(x_2, x_5);
x_15 = l_Lean_Compiler_LCNF_toLCNFType(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_isErased(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_push(x_23, x_5);
x_25 = lean_expr_abstract(x_16, x_24);
lean_dec(x_24);
lean_dec(x_16);
x_26 = l_Lean_Expr_lam___override(x_3, x_12, x_25, x_4);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_array_push(x_28, x_5);
x_30 = lean_expr_abstract(x_16, x_29);
lean_dec(x_29);
lean_dec(x_16);
x_31 = l_Lean_Expr_lam___override(x_3, x_12, x_30, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_17);
return x_32;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
return x_15;
}
}
else
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
return x_15;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Compiler_LCNF_toLCNFType_whnfEta(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = l_Lean_Compiler_LCNF_toLCNFType_visitApp(x_12, x_15, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_15);
return x_16;
}
case 3:
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l_Lean_Expr_sort___override(x_19);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l_Lean_Expr_sort___override(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = l_Lean_Compiler_LCNF_toLCNFType_visitApp(x_12, x_27, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = l_Lean_Expr_sort___override(x_30);
x_32 = l_Lean_Expr_getAppNumArgs(x_12);
lean_inc(x_32);
x_33 = lean_mk_array(x_32, x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_32, x_34);
lean_dec(x_32);
x_36 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toLCNFType_spec__0(x_12, x_33, x_35, x_2, x_3, x_4, x_5, x_29);
return x_36;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 8);
lean_dec(x_12);
x_42 = lean_box(x_41);
lean_inc(x_38);
lean_inc(x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed), 10, 4);
lean_closure_set(x_43, 0, x_39);
lean_closure_set(x_43, 1, x_40);
lean_closure_set(x_43, 2, x_38);
lean_closure_set(x_43, 3, x_42);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_Meta_withLocalDecl___at___Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(x_38, x_41, x_39, x_43, x_45, x_2, x_3, x_4, x_5, x_37);
return x_46;
}
case 7:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_dec(x_11);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
x_50 = l_Lean_Compiler_LCNF_toLCNFType_visitForall(x_12, x_49, x_2, x_3, x_4, x_5, x_47);
return x_50;
}
default: 
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_53 = lean_mk_string_unchecked("lcAny", 5, 5);
x_54 = l_Lean_Name_mkStr1(x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
lean_ctor_set(x_11, 0, x_56);
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_mk_string_unchecked("lcAny", 5, 5);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Expr_const___override(x_59, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_7);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
x_65 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_7, 0, x_65);
return x_7;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_dec(x_7);
x_67 = l_Lean_Compiler_LCNF_erasedExpr;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_20 = l_Lean_Meta_isProp(x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_24 = l_Lean_Compiler_LCNF_isPropFormer(x_19, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_28 = l_Lean_Meta_isTypeFormer(x_19, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_mk_string_unchecked("lcAny", 5, 5);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Expr_const___override(x_33, x_34);
x_36 = l_Lean_Expr_app___override(x_4, x_35);
x_10 = x_36;
x_11 = x_31;
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_38 = l_Lean_Compiler_LCNF_toLCNFType(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_4, x_39);
x_10 = x_41;
x_11 = x_40;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_19);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_dec(x_24);
x_47 = l_Lean_Compiler_LCNF_erasedExpr;
x_48 = l_Lean_Expr_app___override(x_4, x_47);
x_10 = x_48;
x_11 = x_46;
goto block_16;
}
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = l_Lean_Compiler_LCNF_erasedExpr;
x_55 = l_Lean_Expr_app___override(x_4, x_54);
x_10 = x_55;
x_11 = x_53;
goto block_16;
}
}
else
{
uint8_t x_56; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
return x_20;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0(x_1, x_8, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_9);
x_11 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_const___override(x_9, x_10);
x_15 = l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0(x_2, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Compiler_LCNF_anyExpr;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
default: 
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = l_Lean_Compiler_LCNF_anyExpr;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Compiler_LCNF_toLCNFType___lam__0(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toLCNFType_visitApp_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_toLCNFType_visitApp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_toLCNFType_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_joinTypes_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("lcAny", 5, 5);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("lcAny", 5, 5);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_bvar___override(x_1);
x_9 = lean_apply_2(x_2, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_fvar___override(x_1);
x_9 = lean_apply_2(x_2, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_mvar___override(x_1);
x_9 = lean_apply_2(x_2, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_sort___override(x_1);
x_9 = lean_apply_2(x_2, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_const___override(x_1, x_2);
x_10 = lean_apply_2(x_3, x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_app___override(x_1, x_2);
x_10 = lean_apply_2(x_3, x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
x_13 = lean_apply_2(x_6, x_12, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_lit___override(x_1);
x_9 = lean_apply_2(x_2, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_11 = lean_apply_2(x_4, x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; uint8_t x_11; uint8_t x_314; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0___boxed), 2, 0);
x_314 = l_Lean_Expr_isErased(x_1);
if (x_314 == 0)
{
uint8_t x_315; 
x_315 = l_Lean_Expr_isErased(x_2);
x_11 = x_315;
goto block_313;
}
else
{
x_11 = x_314;
goto block_313;
}
block_9:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("lcAny", 5, 5);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
return x_3;
}
}
block_313:
{
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_expr_eqv(x_1, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_14 = l_Lean_Expr_headBeta(x_2);
x_15 = lean_expr_eqv(x_1, x_13);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
if (x_12 == 0)
{
uint8_t x_17; 
x_17 = lean_expr_eqv(x_2, x_14);
if (x_17 == 0)
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_24 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1(x_19, x_10, x_2, x_20, x_21, x_22, x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_30 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1(x_25, x_10, x_2, x_26, x_27, x_28, x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
return x_30;
}
case 10:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_Expr_bvar___override(x_31);
x_1 = x_33;
x_2 = x_32;
goto _start;
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Expr_bvar___override(x_35);
x_37 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_36, x_2);
lean_dec(x_2);
lean_dec(x_36);
return x_37;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_43 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2(x_38, x_10, x_2, x_39, x_40, x_41, x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
return x_43;
}
case 7:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_49 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2(x_44, x_10, x_2, x_45, x_46, x_47, x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
return x_49;
}
case 10:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Lean_Expr_fvar___override(x_50);
x_1 = x_52;
x_2 = x_51;
goto _start;
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_Expr_fvar___override(x_54);
x_56 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_55, x_2);
lean_dec(x_2);
lean_dec(x_55);
return x_56;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_62 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3(x_57, x_10, x_2, x_58, x_59, x_60, x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
return x_62;
}
case 7:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_68 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3(x_63, x_10, x_2, x_64, x_65, x_66, x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
return x_68;
}
case 10:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_10);
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_Expr_mvar___override(x_69);
x_1 = x_71;
x_2 = x_70;
goto _start;
}
default: 
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l_Lean_Expr_mvar___override(x_73);
x_75 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_74, x_2);
lean_dec(x_2);
lean_dec(x_74);
return x_75;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_81 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4(x_76, x_10, x_2, x_77, x_78, x_79, x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
return x_81;
}
case 7:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_87 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4(x_82, x_10, x_2, x_83, x_84, x_85, x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
return x_87;
}
case 10:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_10);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l_Lean_Expr_sort___override(x_88);
x_1 = x_90;
x_2 = x_89;
goto _start;
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_10);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_Lean_Expr_sort___override(x_92);
x_94 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_93, x_2);
lean_dec(x_2);
lean_dec(x_93);
return x_94;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_101 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5(x_95, x_96, x_10, x_2, x_97, x_98, x_99, x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_101;
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
lean_dec(x_1);
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 2);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_108 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5(x_102, x_103, x_10, x_2, x_104, x_105, x_106, x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_108;
}
case 10:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_10);
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
lean_dec(x_1);
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
lean_dec(x_2);
x_112 = l_Lean_Expr_const___override(x_109, x_110);
x_1 = x_112;
x_2 = x_111;
goto _start;
}
default: 
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_10);
x_114 = lean_ctor_get(x_1, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_dec(x_1);
x_116 = l_Lean_Expr_const___override(x_114, x_115);
x_117 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_116, x_2);
lean_dec(x_2);
lean_dec(x_116);
return x_117;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_10);
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
lean_dec(x_1);
x_120 = lean_ctor_get(x_2, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
lean_dec(x_2);
x_122 = l_Lean_Compiler_LCNF_joinTypes_x3f(x_118, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_dec(x_121);
lean_dec(x_119);
x_3 = x_122;
goto block_9;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Lean_Compiler_LCNF_joinTypes_x3f(x_119, x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_123);
x_3 = x_124;
goto block_9;
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = l_Lean_Expr_app___override(x_123, x_126);
lean_ctor_set(x_124, 0, x_127);
return x_124;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
lean_dec(x_124);
x_129 = l_Lean_Expr_app___override(x_123, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
case 6:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
lean_dec(x_1);
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 2);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_137 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6(x_131, x_132, x_10, x_2, x_133, x_134, x_135, x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
return x_137;
}
case 7:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
lean_dec(x_1);
x_140 = lean_ctor_get(x_2, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_2, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 2);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_144 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6(x_138, x_139, x_10, x_2, x_140, x_141, x_142, x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
return x_144;
}
case 10:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_10);
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_ctor_get(x_2, 1);
lean_inc(x_147);
lean_dec(x_2);
x_148 = l_Lean_Expr_app___override(x_145, x_146);
x_1 = x_148;
x_2 = x_147;
goto _start;
}
default: 
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_10);
x_150 = lean_ctor_get(x_1, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_1, 1);
lean_inc(x_151);
lean_dec(x_1);
x_152 = l_Lean_Expr_app___override(x_150, x_151);
x_153 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_152, x_2);
lean_dec(x_2);
lean_dec(x_152);
return x_153;
}
}
}
case 6:
{
lean_dec(x_10);
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_1, 2);
lean_inc(x_156);
lean_dec(x_1);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_2, 2);
lean_inc(x_158);
lean_dec(x_2);
x_159 = l_Lean_Compiler_LCNF_joinTypes_x3f(x_155, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_mk_string_unchecked("lcAny", 5, 5);
x_161 = l_Lean_Name_mkStr1(x_160);
x_162 = lean_box(0);
x_163 = l_Lean_Expr_const___override(x_161, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
return x_159;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_159);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_159, 0);
x_167 = l_Lean_Compiler_LCNF_joinTypes(x_156, x_158);
x_168 = lean_box(0);
x_169 = lean_unbox(x_168);
x_170 = l_Lean_Expr_lam___override(x_154, x_166, x_167, x_169);
lean_ctor_set(x_159, 0, x_170);
return x_159;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_159, 0);
lean_inc(x_171);
lean_dec(x_159);
x_172 = l_Lean_Compiler_LCNF_joinTypes(x_156, x_158);
x_173 = lean_box(0);
x_174 = lean_unbox(x_173);
x_175 = l_Lean_Expr_lam___override(x_154, x_171, x_172, x_174);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
case 10:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_1, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_1, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 2);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
lean_dec(x_2);
x_182 = l_Lean_Expr_lam___override(x_177, x_178, x_179, x_180);
x_1 = x_182;
x_2 = x_181;
goto _start;
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 2);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_188 = l_Lean_Expr_lam___override(x_184, x_185, x_186, x_187);
x_189 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_188, x_2);
lean_dec(x_2);
lean_dec(x_188);
return x_189;
}
}
}
case 7:
{
lean_dec(x_10);
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_1, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_1, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_1, 2);
lean_inc(x_192);
lean_dec(x_1);
x_193 = lean_ctor_get(x_2, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_2, 2);
lean_inc(x_194);
lean_dec(x_2);
x_195 = l_Lean_Compiler_LCNF_joinTypes_x3f(x_191, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_190);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_mk_string_unchecked("lcAny", 5, 5);
x_197 = l_Lean_Name_mkStr1(x_196);
x_198 = lean_box(0);
x_199 = l_Lean_Expr_const___override(x_197, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
else
{
return x_195;
}
}
else
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_195);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_195, 0);
x_203 = l_Lean_Compiler_LCNF_joinTypes(x_192, x_194);
x_204 = lean_box(0);
x_205 = lean_unbox(x_204);
x_206 = l_Lean_Expr_forallE___override(x_190, x_202, x_203, x_205);
lean_ctor_set(x_195, 0, x_206);
return x_195;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_195, 0);
lean_inc(x_207);
lean_dec(x_195);
x_208 = l_Lean_Compiler_LCNF_joinTypes(x_192, x_194);
x_209 = lean_box(0);
x_210 = lean_unbox(x_209);
x_211 = l_Lean_Expr_forallE___override(x_190, x_207, x_208, x_210);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
case 10:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_1, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_1, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_1, 2);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_217 = lean_ctor_get(x_2, 1);
lean_inc(x_217);
lean_dec(x_2);
x_218 = l_Lean_Expr_forallE___override(x_213, x_214, x_215, x_216);
x_1 = x_218;
x_2 = x_217;
goto _start;
}
default: 
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_1, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_1, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_1, 2);
lean_inc(x_222);
x_223 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_224 = l_Lean_Expr_forallE___override(x_220, x_221, x_222, x_223);
x_225 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_224, x_2);
lean_dec(x_2);
lean_dec(x_224);
return x_225;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_1, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_1, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 3);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_231 = lean_ctor_get(x_2, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_2, 2);
lean_inc(x_233);
x_234 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_235 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7(x_226, x_227, x_228, x_229, x_230, x_10, x_2, x_231, x_232, x_233, x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
return x_235;
}
case 7:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_1, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_1, 3);
lean_inc(x_239);
x_240 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_2, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_245 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7(x_236, x_237, x_238, x_239, x_240, x_10, x_2, x_241, x_242, x_243, x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
return x_245;
}
case 10:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_10);
x_246 = lean_ctor_get(x_1, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_1, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_1, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_1, 3);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_251 = lean_ctor_get(x_2, 1);
lean_inc(x_251);
lean_dec(x_2);
x_252 = l_Lean_Expr_letE___override(x_246, x_247, x_248, x_249, x_250);
x_1 = x_252;
x_2 = x_251;
goto _start;
}
default: 
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_10);
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_1, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_1, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_1, 3);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_259 = l_Lean_Expr_letE___override(x_254, x_255, x_256, x_257, x_258);
x_260 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_259, x_2);
lean_dec(x_2);
lean_dec(x_259);
return x_260;
}
}
}
case 9:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_1, 0);
lean_inc(x_261);
lean_dec(x_1);
x_262 = lean_ctor_get(x_2, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_2, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_2, 2);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_266 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8(x_261, x_10, x_2, x_262, x_263, x_264, x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
return x_266;
}
case 7:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
lean_dec(x_1);
x_268 = lean_ctor_get(x_2, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_2, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_2, 2);
lean_inc(x_270);
x_271 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_272 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8(x_267, x_10, x_2, x_268, x_269, x_270, x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
return x_272;
}
case 10:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_10);
x_273 = lean_ctor_get(x_1, 0);
lean_inc(x_273);
lean_dec(x_1);
x_274 = lean_ctor_get(x_2, 1);
lean_inc(x_274);
lean_dec(x_2);
x_275 = l_Lean_Expr_lit___override(x_273);
x_1 = x_275;
x_2 = x_274;
goto _start;
}
default: 
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_10);
x_277 = lean_ctor_get(x_1, 0);
lean_inc(x_277);
lean_dec(x_1);
x_278 = l_Lean_Expr_lit___override(x_277);
x_279 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_278, x_2);
lean_dec(x_2);
lean_dec(x_278);
return x_279;
}
}
}
case 10:
{
lean_object* x_280; 
lean_dec(x_10);
x_280 = lean_ctor_get(x_1, 1);
lean_inc(x_280);
lean_dec(x_1);
x_1 = x_280;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_282 = lean_ctor_get(x_1, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_1, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_1, 2);
lean_inc(x_284);
lean_dec(x_1);
x_285 = lean_ctor_get(x_2, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_2, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_2, 2);
lean_inc(x_287);
x_288 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_289 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9(x_282, x_283, x_284, x_10, x_2, x_285, x_286, x_287, x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
return x_289;
}
case 7:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; 
x_290 = lean_ctor_get(x_1, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_1, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_1, 2);
lean_inc(x_292);
lean_dec(x_1);
x_293 = lean_ctor_get(x_2, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_2, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_2, 2);
lean_inc(x_295);
x_296 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_297 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9(x_290, x_291, x_292, x_10, x_2, x_293, x_294, x_295, x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
return x_297;
}
case 10:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_10);
x_298 = lean_ctor_get(x_1, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_1, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_1, 2);
lean_inc(x_300);
lean_dec(x_1);
x_301 = lean_ctor_get(x_2, 1);
lean_inc(x_301);
lean_dec(x_2);
x_302 = l_Lean_Expr_proj___override(x_298, x_299, x_300);
x_1 = x_302;
x_2 = x_301;
goto _start;
}
default: 
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_10);
x_304 = lean_ctor_get(x_1, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_1, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_1, 2);
lean_inc(x_306);
lean_dec(x_1);
x_307 = l_Lean_Expr_proj___override(x_304, x_305, x_306);
x_308 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_307, x_2);
lean_dec(x_2);
lean_dec(x_307);
return x_308;
}
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
}
}
else
{
lean_object* x_310; 
lean_dec(x_10);
lean_dec(x_2);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_1);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_311 = l_Lean_Compiler_LCNF_erasedExpr;
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_11);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__7(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_joinTypes_x3f___lam__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_1 = x_5;
goto _start;
}
default: 
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_isTypeFormerType(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("invalid instantiateForall, too many parameters", 46, 46);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Expr_headBeta(x_3);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Expr_bvar___override(x_11);
x_13 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_12, x_4, x_5, x_6);
lean_dec(x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Expr_fvar___override(x_14);
x_16 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_15, x_4, x_5, x_6);
lean_dec(x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Expr_mvar___override(x_17);
x_19 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Expr_sort___override(x_20);
x_22 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_21, x_4, x_5, x_6);
lean_dec(x_21);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_Expr_const___override(x_23, x_24);
x_26 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_25, x_4, x_5, x_6);
lean_dec(x_25);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = l_Lean_Expr_app___override(x_27, x_28);
x_30 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_29, x_4, x_5, x_6);
lean_dec(x_29);
return x_30;
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 8);
lean_dec(x_10);
x_35 = l_Lean_Expr_lam___override(x_31, x_32, x_33, x_34);
x_36 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_35, x_4, x_5, x_6);
lean_dec(x_35);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_10, 2);
lean_inc(x_37);
lean_dec(x_10);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
x_40 = lean_array_fget(x_1, x_2);
lean_dec(x_2);
x_41 = lean_expr_instantiate1(x_37, x_40);
lean_dec(x_40);
lean_dec(x_37);
x_2 = x_39;
x_3 = x_41;
goto _start;
}
case 8:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 3);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_10, sizeof(void*)*4 + 8);
lean_dec(x_10);
x_48 = l_Lean_Expr_letE___override(x_43, x_44, x_45, x_46, x_47);
x_49 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_48, x_4, x_5, x_6);
lean_dec(x_48);
return x_49;
}
case 9:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_50 = lean_ctor_get(x_10, 0);
lean_inc(x_50);
lean_dec(x_10);
x_51 = l_Lean_Expr_lit___override(x_50);
x_52 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_51, x_4, x_5, x_6);
lean_dec(x_51);
return x_52;
}
case 10:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_dec(x_10);
x_55 = l_Lean_Expr_mdata___override(x_53, x_54);
x_56 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_55, x_4, x_5, x_6);
lean_dec(x_55);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_10, 2);
lean_inc(x_59);
lean_dec(x_10);
x_60 = l_Lean_Expr_proj___override(x_57, x_58, x_59);
x_61 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_60, x_4, x_5, x_6);
lean_dec(x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_instantiateForall_go___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_instantiateForall_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Compiler_LCNF_instantiateForall_go(x_2, x_6, x_1, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_instantiateForall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 7:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_1 = x_8;
goto _start;
}
default: 
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_isPredicateType(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
case 7:
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_1 = x_5;
goto _start;
}
default: 
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = l_Lean_Expr_isErased(x_1);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_maybeTypeFormerType(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_5);
x_10 = lean_is_class(x_9, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
x_16 = lean_is_class(x_15, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isClass_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_isClass_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isClass_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Expr_headBeta(x_1);
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Lean_Compiler_LCNF_isClass_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isArrowClass_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headBeta(x_1);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Compiler_LCNF_getArrowArity(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Environment_find_x3f(x_13, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_InductiveVal_numCtors(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_dec(x_17);
goto block_12;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_9;
}
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_term_u25fe = _init_l_Lean_Compiler_term_u25fe();
lean_mark_persistent(l_Lean_Compiler_term_u25fe);
l_Lean_Compiler_LCNF_erasedExpr = _init_l_Lean_Compiler_LCNF_erasedExpr();
lean_mark_persistent(l_Lean_Compiler_LCNF_erasedExpr);
l_Lean_Compiler_LCNF_anyExpr = _init_l_Lean_Compiler_LCNF_anyExpr();
lean_mark_persistent(l_Lean_Compiler_LCNF_anyExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
