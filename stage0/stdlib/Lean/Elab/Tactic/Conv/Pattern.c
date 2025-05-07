// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Pattern
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Conv.Basic Lean.HeadIndex
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__9(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Array_allDiff___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_visitFn_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__8___boxed(lean_object**);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1(size_t, size_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Meta_getSimpCongrTheorems(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_Simp_neutralConfig;
x_10 = l_Array_empty(lean_box(0));
x_11 = l_Lean_Meta_Simp_mkContext(x_9, x_10, x_7, x_1, x_2, x_3, x_4, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_Lean_Expr_toHeadIndex(x_2);
lean_inc(x_1);
x_9 = l_Lean_Expr_toHeadIndex(x_1);
x_10 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = l_Lean_Expr_isApp(x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_13);
x_21 = l_Lean_Expr_appFn_x21(x_2);
x_22 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(x_1, x_21, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_2);
return x_22;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_31 = lean_array_push(x_29, x_30);
lean_ctor_set(x_26, 1, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_22;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_43 = lean_array_push(x_40, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_23, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_23, 0);
lean_inc(x_46);
lean_dec(x_23);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_48 = x_22;
} else {
 lean_dec_ref(x_22);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_53 = lean_array_push(x_50, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_48)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_48;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
}
}
else
{
lean_dec(x_2);
return x_22;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_dec(x_13);
x_58 = l_Lean_Expr_isApp(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_appFn_x21(x_2);
x_62 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(x_1, x_61, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_2);
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_72 = lean_array_push(x_69, x_71);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_67;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
}
else
{
lean_dec(x_2);
return x_62;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_13);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_13, 0);
lean_dec(x_77);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_mk_empty_array_with_capacity(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_13, 0, x_81);
return x_13;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_dec(x_13);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_mk_empty_array_with_capacity(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_13);
if (x_88 == 0)
{
return x_13;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_13, 0);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint8_t x_39; uint64_t x_40; uint64_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_3);
x_8 = l_Lean_Meta_openAbstractMVarsResult(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(2);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, 0);
x_16 = lean_ctor_get_uint8(x_14, 1);
x_17 = lean_ctor_get_uint8(x_14, 2);
x_18 = lean_ctor_get_uint8(x_14, 3);
x_19 = lean_ctor_get_uint8(x_14, 4);
x_20 = lean_ctor_get_uint8(x_14, 5);
x_21 = lean_ctor_get_uint8(x_14, 6);
x_22 = lean_ctor_get_uint8(x_14, 7);
x_23 = lean_ctor_get_uint8(x_14, 8);
x_24 = lean_ctor_get_uint8(x_14, 10);
x_25 = lean_ctor_get_uint8(x_14, 11);
x_26 = lean_ctor_get_uint8(x_14, 12);
x_27 = lean_ctor_get_uint8(x_14, 13);
x_28 = lean_ctor_get_uint8(x_14, 14);
x_29 = lean_ctor_get_uint8(x_14, 15);
x_30 = lean_ctor_get_uint8(x_14, 16);
x_31 = lean_ctor_get_uint8(x_14, 17);
lean_dec(x_14);
x_32 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_32, 0, x_15);
lean_ctor_set_uint8(x_32, 1, x_16);
lean_ctor_set_uint8(x_32, 2, x_17);
lean_ctor_set_uint8(x_32, 3, x_18);
lean_ctor_set_uint8(x_32, 4, x_19);
lean_ctor_set_uint8(x_32, 5, x_20);
lean_ctor_set_uint8(x_32, 6, x_21);
lean_ctor_set_uint8(x_32, 7, x_22);
lean_ctor_set_uint8(x_32, 8, x_23);
x_33 = lean_unbox(x_13);
lean_ctor_set_uint8(x_32, 9, x_33);
lean_ctor_set_uint8(x_32, 10, x_24);
lean_ctor_set_uint8(x_32, 11, x_25);
lean_ctor_set_uint8(x_32, 12, x_26);
lean_ctor_set_uint8(x_32, 13, x_27);
lean_ctor_set_uint8(x_32, 14, x_28);
lean_ctor_set_uint8(x_32, 15, x_29);
lean_ctor_set_uint8(x_32, 16, x_30);
lean_ctor_set_uint8(x_32, 17, x_31);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_shift_right(x_34, x_36);
x_38 = lean_uint64_shift_left(x_37, x_36);
x_39 = lean_unbox(x_13);
x_40 = l_Lean_Meta_TransparencyMode_toUInt64(x_39);
x_41 = lean_uint64_lor(x_38, x_40);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 6);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
lean_ctor_set_uint64(x_51, sizeof(void*)*7, x_41);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 9, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 10, x_50);
x_52 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(x_12, x_2, x_51, x_4, x_5, x_6, x_11);
lean_dec(x_51);
return x_52;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_8, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_List_isEmpty___redArg(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_nat_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 0, x_17);
x_19 = lean_array_push(x_12, x_10);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_13, x_20);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_15);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = lean_array_push(x_12, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_13, x_25);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_15);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_24);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_31 = x_10;
} else {
 lean_dec_ref(x_10);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_1);
x_33 = lean_array_push(x_27, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_28, x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_29);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(x_14);
lean_dec(x_14);
x_17 = lean_box(1);
if (x_16 == 0)
{
lean_object* x_18; 
lean_free_object(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(x_1, x_3, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(x_2, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_32);
lean_dec(x_31);
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = lean_st_ref_take(x_2, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(x_38);
x_41 = lean_st_ref_set(x_2, x_40, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_31, x_50, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_st_ref_take(x_2, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_mvarId_x21(x_55);
x_60 = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(x_59, x_57);
x_61 = lean_st_ref_set(x_2, x_60, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_array_size(x_32);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_visitFn_spec__0(x_32, x_63, x_65, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lean_mkAppN(x_54, x_32);
lean_dec(x_32);
lean_ctor_set(x_19, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_19);
x_71 = lean_unbox(x_17);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_71);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_66, 0, x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_66);
x_75 = l_Lean_mkAppN(x_54, x_32);
lean_dec(x_32);
lean_ctor_set(x_19, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_19);
x_77 = lean_unbox(x_17);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_77);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_54);
lean_dec(x_32);
lean_free_object(x_19);
x_80 = !lean_is_exclusive(x_66);
if (x_80 == 0)
{
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_66, 0);
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_66);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
return x_51;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_51, 0);
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_51);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_19, 0);
lean_inc(x_88);
lean_dec(x_19);
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_dec(x_18);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(x_2, x_89);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(x_93);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = lean_st_ref_take(x_2, x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(x_97);
x_100 = lean_st_ref_set(x_2, x_99, x_98);
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
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_107 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_90, x_106, x_7, x_8, x_9, x_10, x_94);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; size_t x_119; lean_object* x_120; size_t x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_st_ref_take(x_2, x_109);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_mvarId_x21(x_111);
x_116 = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(x_115, x_113);
x_117 = lean_st_ref_set(x_2, x_116, x_114);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_array_size(x_91);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_usize_of_nat(x_120);
x_122 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_visitFn_spec__0(x_91, x_119, x_121, x_111, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_118);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_mkAppN(x_110, x_91);
lean_dec(x_91);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_123);
x_128 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_unbox(x_17);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_129);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_128);
if (lean_is_scalar(x_125)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_125;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_124);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_110);
lean_dec(x_91);
x_132 = lean_ctor_get(x_122, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_134 = x_122;
} else {
 lean_dec_ref(x_122);
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
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_136 = lean_ctor_get(x_107, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_107, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_138 = x_107;
} else {
 lean_dec_ref(x_107);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_140 = !lean_is_exclusive(x_18);
if (x_140 == 0)
{
return x_18;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_18, 0);
x_142 = lean_ctor_get(x_18, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_18);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_145, 0, x_3);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unbox(x_17);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_146);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_12, 0, x_147);
return x_12;
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_12, 0);
x_149 = lean_ctor_get(x_12, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_12);
x_150 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(x_148);
lean_dec(x_148);
x_151 = lean_box(1);
if (x_150 == 0)
{
lean_object* x_152; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_152 = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(x_1, x_3, x_7, x_8, x_9, x_10, x_149);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_159 = lean_ctor_get(x_153, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_160 = x_153;
} else {
 lean_dec_ref(x_153);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
lean_dec(x_152);
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(x_2, x_161);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(x_165);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_168 = lean_st_ref_take(x_2, x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(x_169);
x_172 = lean_st_ref_set(x_2, x_171, x_170);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_176, 0, x_175);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_179 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_162, x_178, x_7, x_8, x_9, x_10, x_166);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; size_t x_191; lean_object* x_192; size_t x_193; lean_object* x_194; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_st_ref_take(x_2, x_181);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Expr_mvarId_x21(x_183);
x_188 = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(x_187, x_185);
x_189 = lean_st_ref_set(x_2, x_188, x_186);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_array_size(x_163);
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_usize_of_nat(x_192);
x_194 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_visitFn_spec__0(x_163, x_191, x_193, x_183, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_190);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; 
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
x_198 = l_Lean_mkAppN(x_182, x_163);
lean_dec(x_163);
if (lean_is_scalar(x_160)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_160;
}
lean_ctor_set(x_199, 0, x_195);
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_unbox(x_151);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_201);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_200);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_196);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_182);
lean_dec(x_163);
lean_dec(x_160);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_194, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_206 = x_194;
} else {
 lean_dec_ref(x_194);
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
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_208 = lean_ctor_get(x_179, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_179, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_210 = x_179;
} else {
 lean_dec_ref(x_179);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_212 = lean_ctor_get(x_152, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_152, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_214 = x_152;
} else {
 lean_dec_ref(x_152);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_217, 0, x_3);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_unbox(x_151);
lean_ctor_set_uint8(x_217, sizeof(void*)*2, x_218);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_217);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_149);
return x_220;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 1)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_25 = lean_array_fget(x_1, x_3);
x_26 = l_Lean_TSyntax_getNat(x_25);
x_27 = lean_nat_dec_eq(x_26, x_14);
if (x_27 == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_mk_string_unchecked("positive integer expected", 25, 25);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_25, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_35 = lean_nat_sub(x_26, x_17);
lean_dec(x_26);
lean_inc(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_19 = x_36;
x_20 = x_13;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_22 = lean_array_push(x_4, x_19);
x_2 = x_18;
x_3 = x_21;
x_4 = x_22;
x_13 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 1)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
x_25 = lean_array_fget(x_1, x_3);
x_26 = l_Lean_TSyntax_getNat(x_25);
x_27 = lean_nat_dec_eq(x_26, x_14);
if (x_27 == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_mk_string_unchecked("positive integer expected", 25, 25);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_25, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_35 = lean_nat_sub(x_26, x_17);
lean_dec(x_26);
lean_inc(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_19 = x_36;
x_20 = x_13;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_22 = lean_array_push(x_4, x_19);
x_23 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(x_1, x_18, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_abstractMVars(x_12, x_3, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_replaceRef(x_1, x_10);
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 2);
x_15 = lean_ctor_get(x_7, 3);
x_16 = lean_ctor_get(x_7, 4);
x_17 = lean_ctor_get(x_7, 6);
x_18 = lean_ctor_get(x_7, 7);
x_19 = lean_ctor_get(x_7, 8);
x_20 = lean_ctor_get(x_7, 9);
x_21 = lean_ctor_get(x_7, 10);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_23 = lean_ctor_get(x_7, 11);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_7, 12);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_26 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_14);
lean_ctor_set(x_26, 3, x_15);
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 5, x_11);
lean_ctor_set(x_26, 6, x_17);
lean_ctor_set(x_26, 7, x_18);
lean_ctor_set(x_26, 8, x_19);
lean_ctor_set(x_26, 9, x_20);
lean_ctor_set(x_26, 10, x_21);
lean_ctor_set(x_26, 11, x_23);
lean_ctor_set(x_26, 12, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*13, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*13 + 1, x_24);
x_27 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_12 = l_Lean_Elab_Tactic_Conv_getRhs(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_mvarId_x21(x_13);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_Simp_Result_getProof(x_1, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_array_to_list(x_2);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_27, x_4, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc(x_11);
x_53 = lean_st_mk_ref(x_11, x_20);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(x_16, x_17, x_18, x_19, x_55);
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
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_11);
x_61 = x_9;
goto block_312;
}
else
{
lean_object* x_313; uint8_t x_314; 
lean_dec(x_11);
x_313 = lean_box(0);
x_314 = lean_unbox(x_313);
x_61 = x_314;
goto block_312;
}
block_36:
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_array_size(x_31);
x_33 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_34 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1(x_32, x_33, x_31);
x_35 = lean_apply_10(x_26, x_34, x_24, x_27, x_25, x_30, x_29, x_28, x_22, x_23, x_21);
return x_35;
}
block_52:
{
lean_object* x_51; 
lean_dec(x_43);
x_51 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(x_37, x_50, x_41);
lean_dec(x_41);
x_21 = x_38;
x_22 = x_44;
x_23 = x_39;
x_24 = x_45;
x_25 = x_46;
x_26 = x_40;
x_27 = x_47;
x_28 = x_42;
x_29 = x_48;
x_30 = x_49;
x_31 = x_51;
goto block_36;
}
block_312:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_62 = l_Lean_Meta_Simp_Context_setMemoize(x_58, x_61);
lean_dec(x_58);
x_63 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_inc(x_1);
lean_inc(x_64);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_1);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_67 = lean_unsigned_to_nat(5u);
x_68 = lean_usize_of_nat(x_67);
x_69 = lean_usize_to_nat(x_68);
x_70 = lean_nat_pow(x_3, x_69);
lean_dec(x_69);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = lean_usize_to_nat(x_71);
x_73 = lean_mk_empty_array_with_capacity(x_72);
lean_dec(x_72);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc_n(x_1, 2);
x_75 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_1);
lean_ctor_set(x_75, 3, x_1);
lean_ctor_set_usize(x_75, 4, x_68);
lean_inc(x_64);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_64);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_75);
if (lean_is_scalar(x_56)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_56;
}
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_54);
lean_inc(x_4);
x_78 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(x_78, 0, x_4);
lean_closure_set(x_78, 1, x_54);
x_79 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_5);
lean_ctor_set(x_79, 2, x_6);
lean_ctor_set(x_79, 3, x_7);
lean_ctor_set(x_79, 4, x_8);
lean_ctor_set_uint8(x_79, sizeof(void*)*5, x_9);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_80 = l_Lean_Meta_Simp_main(x_10, x_62, x_77, x_79, x_16, x_17, x_18, x_19, x_59);
lean_dec(x_77);
lean_dec(x_62);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_dec(x_85);
x_86 = lean_st_ref_get(x_54, x_82);
lean_dec(x_54);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_84);
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__7___boxed), 11, 1);
lean_closure_set(x_90, 0, x_84);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_90);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_array_get_size(x_91);
x_93 = lean_nat_dec_eq(x_92, x_1);
lean_dec(x_1);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_free_object(x_86);
lean_free_object(x_81);
lean_dec(x_4);
x_94 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(x_84, x_91, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_91);
lean_dec(x_84);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_95 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = lean_ctor_get(x_4, 2);
lean_inc(x_97);
lean_dec(x_4);
x_98 = l_Lean_indentExpr(x_97);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_98);
lean_ctor_set(x_86, 0, x_96);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_100);
lean_ctor_set(x_81, 0, x_86);
x_101 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_81, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_84);
x_106 = lean_ctor_get(x_88, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_88, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_88, 2);
lean_inc(x_108);
lean_dec(x_88);
x_109 = lean_nat_dec_eq(x_107, x_1);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_4);
x_110 = l_List_getLast_x3f___redArg(x_108);
lean_dec(x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_107);
lean_free_object(x_86);
lean_free_object(x_81);
x_111 = lean_array_get_size(x_106);
x_112 = lean_nat_dec_eq(x_111, x_1);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_nat_sub(x_111, x_2);
x_114 = lean_nat_dec_le(x_1, x_113);
if (x_114 == 0)
{
lean_inc(x_113);
x_37 = x_106;
x_38 = x_89;
x_39 = x_19;
x_40 = x_90;
x_41 = x_113;
x_42 = x_17;
x_43 = x_111;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_113;
goto block_52;
}
else
{
lean_inc(x_1);
x_37 = x_106;
x_38 = x_89;
x_39 = x_19;
x_40 = x_90;
x_41 = x_113;
x_42 = x_17;
x_43 = x_111;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_1;
goto block_52;
}
}
else
{
lean_dec(x_111);
x_21 = x_89;
x_22 = x_18;
x_23 = x_19;
x_24 = x_12;
x_25 = x_14;
x_26 = x_90;
x_27 = x_13;
x_28 = x_17;
x_29 = x_16;
x_30 = x_15;
x_31 = x_106;
goto block_36;
}
}
else
{
uint8_t x_115; 
lean_dec(x_106);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
lean_dec(x_119);
x_120 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was found only ", 53, 53);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_122 = l___private_Init_Data_Repr_0__Nat_reprFast(x_107);
lean_ctor_set_tag(x_110, 3);
lean_ctor_set(x_110, 0, x_122);
x_123 = l_Lean_MessageData_ofFormat(x_110);
lean_ctor_set_tag(x_116, 7);
lean_ctor_set(x_116, 1, x_123);
lean_ctor_set(x_116, 0, x_121);
x_124 = lean_mk_string_unchecked(" times but ", 11, 11);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_125);
lean_ctor_set(x_86, 0, x_116);
x_126 = lean_nat_add(x_118, x_2);
lean_dec(x_118);
x_127 = l___private_Init_Data_Repr_0__Nat_reprFast(x_126);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_MessageData_ofFormat(x_128);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_129);
lean_ctor_set(x_81, 0, x_86);
x_130 = lean_mk_string_unchecked(" expected", 9, 9);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_81);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_132, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_134 = lean_ctor_get(x_116, 0);
lean_inc(x_134);
lean_dec(x_116);
x_135 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was found only ", 53, 53);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = l___private_Init_Data_Repr_0__Nat_reprFast(x_107);
lean_ctor_set_tag(x_110, 3);
lean_ctor_set(x_110, 0, x_137);
x_138 = l_Lean_MessageData_ofFormat(x_110);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked(" times but ", 11, 11);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_141);
lean_ctor_set(x_86, 0, x_139);
x_142 = lean_nat_add(x_134, x_2);
lean_dec(x_134);
x_143 = l___private_Init_Data_Repr_0__Nat_reprFast(x_142);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_MessageData_ofFormat(x_144);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_145);
lean_ctor_set(x_81, 0, x_86);
x_146 = lean_mk_string_unchecked(" expected", 9, 9);
x_147 = l_Lean_stringToMessageData(x_146);
lean_dec(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_81);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_148, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_150 = lean_ctor_get(x_110, 0);
lean_inc(x_150);
lean_dec(x_110);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was found only ", 53, 53);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = l___private_Init_Data_Repr_0__Nat_reprFast(x_107);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_MessageData_ofFormat(x_156);
if (lean_is_scalar(x_152)) {
 x_158 = lean_alloc_ctor(7, 2, 0);
} else {
 x_158 = x_152;
 lean_ctor_set_tag(x_158, 7);
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked(" times but ", 11, 11);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_160);
lean_ctor_set(x_86, 0, x_158);
x_161 = lean_nat_add(x_151, x_2);
lean_dec(x_151);
x_162 = l___private_Init_Data_Repr_0__Nat_reprFast(x_161);
x_163 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_MessageData_ofFormat(x_163);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_164);
lean_ctor_set(x_81, 0, x_86);
x_165 = lean_mk_string_unchecked(" expected", 9, 9);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_81);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_167, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_169 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_171 = lean_ctor_get(x_4, 2);
lean_inc(x_171);
lean_dec(x_4);
x_172 = l_Lean_indentExpr(x_171);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_172);
lean_ctor_set(x_86, 0, x_170);
x_173 = lean_mk_string_unchecked("", 0, 0);
x_174 = l_Lean_stringToMessageData(x_173);
lean_dec(x_173);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_174);
lean_ctor_set(x_81, 0, x_86);
x_175 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_81, x_16, x_17, x_18, x_19, x_89);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
return x_175;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_175);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_86, 0);
x_181 = lean_ctor_get(x_86, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_86);
lean_inc(x_84);
x_182 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__7___boxed), 11, 1);
lean_closure_set(x_182, 0, x_84);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_182);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_array_get_size(x_183);
x_185 = lean_nat_dec_eq(x_184, x_1);
lean_dec(x_1);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
lean_free_object(x_81);
lean_dec(x_4);
x_186 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(x_84, x_183, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_181);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_183);
lean_dec(x_84);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_187 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_ctor_get(x_4, 2);
lean_inc(x_189);
lean_dec(x_4);
x_190 = l_Lean_indentExpr(x_189);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_193);
lean_ctor_set(x_81, 0, x_191);
x_194 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_81, x_16, x_17, x_18, x_19, x_181);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
lean_dec(x_84);
x_199 = lean_ctor_get(x_180, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_180, 2);
lean_inc(x_201);
lean_dec(x_180);
x_202 = lean_nat_dec_eq(x_200, x_1);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_4);
x_203 = l_List_getLast_x3f___redArg(x_201);
lean_dec(x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
lean_dec(x_200);
lean_free_object(x_81);
x_204 = lean_array_get_size(x_199);
x_205 = lean_nat_dec_eq(x_204, x_1);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_nat_sub(x_204, x_2);
x_207 = lean_nat_dec_le(x_1, x_206);
if (x_207 == 0)
{
lean_inc(x_206);
x_37 = x_199;
x_38 = x_181;
x_39 = x_19;
x_40 = x_182;
x_41 = x_206;
x_42 = x_17;
x_43 = x_204;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_206;
goto block_52;
}
else
{
lean_inc(x_1);
x_37 = x_199;
x_38 = x_181;
x_39 = x_19;
x_40 = x_182;
x_41 = x_206;
x_42 = x_17;
x_43 = x_204;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_1;
goto block_52;
}
}
else
{
lean_dec(x_204);
x_21 = x_181;
x_22 = x_18;
x_23 = x_19;
x_24 = x_12;
x_25 = x_14;
x_26 = x_182;
x_27 = x_13;
x_28 = x_17;
x_29 = x_16;
x_30 = x_15;
x_31 = x_199;
goto block_36;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_199);
lean_dec(x_182);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was found only ", 53, 53);
x_213 = l_Lean_stringToMessageData(x_212);
lean_dec(x_212);
x_214 = l___private_Init_Data_Repr_0__Nat_reprFast(x_200);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(3, 1, 0);
} else {
 x_215 = x_209;
 lean_ctor_set_tag(x_215, 3);
}
lean_ctor_set(x_215, 0, x_214);
x_216 = l_Lean_MessageData_ofFormat(x_215);
if (lean_is_scalar(x_211)) {
 x_217 = lean_alloc_ctor(7, 2, 0);
} else {
 x_217 = x_211;
 lean_ctor_set_tag(x_217, 7);
}
lean_ctor_set(x_217, 0, x_213);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_mk_string_unchecked(" times but ", 11, 11);
x_219 = l_Lean_stringToMessageData(x_218);
lean_dec(x_218);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_nat_add(x_210, x_2);
lean_dec(x_210);
x_222 = l___private_Init_Data_Repr_0__Nat_reprFast(x_221);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Lean_MessageData_ofFormat(x_223);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_224);
lean_ctor_set(x_81, 0, x_220);
x_225 = lean_mk_string_unchecked(" expected", 9, 9);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_81);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_227, x_16, x_17, x_18, x_19, x_181);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_182);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_229 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_230 = l_Lean_stringToMessageData(x_229);
lean_dec(x_229);
x_231 = lean_ctor_get(x_4, 2);
lean_inc(x_231);
lean_dec(x_4);
x_232 = l_Lean_indentExpr(x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_mk_string_unchecked("", 0, 0);
x_235 = l_Lean_stringToMessageData(x_234);
lean_dec(x_234);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_235);
lean_ctor_set(x_81, 0, x_233);
x_236 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_81, x_16, x_17, x_18, x_19, x_181);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_81, 0);
lean_inc(x_241);
lean_dec(x_81);
x_242 = lean_st_ref_get(x_54, x_82);
lean_dec(x_54);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
lean_inc(x_241);
x_246 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__7___boxed), 11, 1);
lean_closure_set(x_246, 0, x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_dec(x_246);
x_247 = lean_ctor_get(x_243, 0);
lean_inc(x_247);
lean_dec(x_243);
x_248 = lean_array_get_size(x_247);
x_249 = lean_nat_dec_eq(x_248, x_1);
lean_dec(x_1);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec(x_245);
lean_dec(x_4);
x_250 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(x_241, x_247, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_244);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_247);
lean_dec(x_241);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_251 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
x_253 = lean_ctor_get(x_4, 2);
lean_inc(x_253);
lean_dec(x_4);
x_254 = l_Lean_indentExpr(x_253);
if (lean_is_scalar(x_245)) {
 x_255 = lean_alloc_ctor(7, 2, 0);
} else {
 x_255 = x_245;
 lean_ctor_set_tag(x_255, 7);
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_mk_string_unchecked("", 0, 0);
x_257 = l_Lean_stringToMessageData(x_256);
lean_dec(x_256);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_258, x_16, x_17, x_18, x_19, x_244);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_dec(x_241);
x_264 = lean_ctor_get(x_243, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_243, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_243, 2);
lean_inc(x_266);
lean_dec(x_243);
x_267 = lean_nat_dec_eq(x_265, x_1);
if (x_267 == 0)
{
lean_object* x_268; 
lean_dec(x_4);
x_268 = l_List_getLast_x3f___redArg(x_266);
lean_dec(x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; uint8_t x_270; 
lean_dec(x_265);
lean_dec(x_245);
x_269 = lean_array_get_size(x_264);
x_270 = lean_nat_dec_eq(x_269, x_1);
if (x_270 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_nat_sub(x_269, x_2);
x_272 = lean_nat_dec_le(x_1, x_271);
if (x_272 == 0)
{
lean_inc(x_271);
x_37 = x_264;
x_38 = x_244;
x_39 = x_19;
x_40 = x_246;
x_41 = x_271;
x_42 = x_17;
x_43 = x_269;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_271;
goto block_52;
}
else
{
lean_inc(x_1);
x_37 = x_264;
x_38 = x_244;
x_39 = x_19;
x_40 = x_246;
x_41 = x_271;
x_42 = x_17;
x_43 = x_269;
x_44 = x_18;
x_45 = x_12;
x_46 = x_14;
x_47 = x_13;
x_48 = x_16;
x_49 = x_15;
x_50 = x_1;
goto block_52;
}
}
else
{
lean_dec(x_269);
x_21 = x_244;
x_22 = x_18;
x_23 = x_19;
x_24 = x_12;
x_25 = x_14;
x_26 = x_246;
x_27 = x_13;
x_28 = x_17;
x_29 = x_16;
x_30 = x_15;
x_31 = x_264;
goto block_36;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_264);
lean_dec(x_246);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was found only ", 53, 53);
x_278 = l_Lean_stringToMessageData(x_277);
lean_dec(x_277);
x_279 = l___private_Init_Data_Repr_0__Nat_reprFast(x_265);
if (lean_is_scalar(x_274)) {
 x_280 = lean_alloc_ctor(3, 1, 0);
} else {
 x_280 = x_274;
 lean_ctor_set_tag(x_280, 3);
}
lean_ctor_set(x_280, 0, x_279);
x_281 = l_Lean_MessageData_ofFormat(x_280);
if (lean_is_scalar(x_276)) {
 x_282 = lean_alloc_ctor(7, 2, 0);
} else {
 x_282 = x_276;
 lean_ctor_set_tag(x_282, 7);
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_mk_string_unchecked(" times but ", 11, 11);
x_284 = l_Lean_stringToMessageData(x_283);
lean_dec(x_283);
if (lean_is_scalar(x_245)) {
 x_285 = lean_alloc_ctor(7, 2, 0);
} else {
 x_285 = x_245;
 lean_ctor_set_tag(x_285, 7);
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_nat_add(x_275, x_2);
lean_dec(x_275);
x_287 = l___private_Init_Data_Repr_0__Nat_reprFast(x_286);
x_288 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = l_Lean_MessageData_ofFormat(x_288);
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_285);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_mk_string_unchecked(" expected", 9, 9);
x_292 = l_Lean_stringToMessageData(x_291);
lean_dec(x_291);
x_293 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_292);
x_294 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_293, x_16, x_17, x_18, x_19, x_244);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_246);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_295 = lean_mk_string_unchecked("'pattern' conv tactic failed, pattern was not found", 51, 51);
x_296 = l_Lean_stringToMessageData(x_295);
lean_dec(x_295);
x_297 = lean_ctor_get(x_4, 2);
lean_inc(x_297);
lean_dec(x_4);
x_298 = l_Lean_indentExpr(x_297);
if (lean_is_scalar(x_245)) {
 x_299 = lean_alloc_ctor(7, 2, 0);
} else {
 x_299 = x_245;
 lean_ctor_set_tag(x_299, 7);
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_mk_string_unchecked("", 0, 0);
x_301 = l_Lean_stringToMessageData(x_300);
lean_dec(x_300);
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_302, x_16, x_17, x_18, x_19, x_244);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_54);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_80);
if (x_308 == 0)
{
return x_80;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_80, 0);
x_310 = lean_ctor_get(x_80, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_80);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (x_1 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_179; uint8_t x_180; 
x_20 = lean_unsigned_to_nat(0u);
x_57 = lean_unsigned_to_nat(1u);
x_179 = l_Lean_Syntax_getArg(x_3, x_57);
x_180 = l_Lean_Syntax_isNone(x_179);
if (x_180 == 0)
{
uint8_t x_181; 
lean_inc(x_179);
x_181 = l_Lean_Syntax_matchesNull(x_179, x_57);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_179);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_182 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_18);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = l_Lean_Syntax_getArg(x_179, x_20);
lean_dec(x_179);
x_184 = lean_mk_string_unchecked("occs", 4, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_185 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_184);
lean_inc(x_183);
x_186 = l_Lean_Syntax_isOfKind(x_183, x_185);
lean_dec(x_185);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_183);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_187 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_18);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_unsigned_to_nat(3u);
x_189 = l_Lean_Syntax_getArg(x_183, x_188);
lean_dec(x_183);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_58 = x_190;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
goto block_178;
}
}
}
else
{
lean_object* x_191; 
lean_dec(x_179);
x_191 = lean_box(0);
x_58 = x_191;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = x_16;
x_66 = x_17;
x_67 = x_18;
goto block_178;
}
block_40:
{
uint8_t x_32; 
x_32 = l_Array_allDiff___redArg(x_2, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
x_33 = lean_mk_string_unchecked("occurrence list is not distinct", 31, 31);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_34, x_29, x_26, x_30, x_22, x_24);
lean_dec(x_22);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_29);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_mk_empty_array_with_capacity(x_20);
x_37 = lean_array_to_list(x_31);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_20);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_apply_10(x_27, x_38, x_28, x_25, x_21, x_23, x_29, x_26, x_30, x_22, x_24);
return x_39;
}
}
block_56:
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(x_43, x_54, x_49);
lean_dec(x_49);
x_21 = x_44;
x_22 = x_45;
x_23 = x_46;
x_24 = x_47;
x_25 = x_48;
x_26 = x_50;
x_27 = x_41;
x_28 = x_51;
x_29 = x_42;
x_30 = x_53;
x_31 = x_55;
goto block_40;
}
block_178:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_68 = lean_unsigned_to_nat(2u);
x_69 = l_Lean_Syntax_getArg(x_3, x_68);
x_70 = lean_box(0);
x_71 = lean_box(x_4);
lean_inc(x_69);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 10, 3);
lean_closure_set(x_72, 0, x_69);
lean_closure_set(x_72, 1, x_70);
lean_closure_set(x_72, 2, x_71);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 9, 2);
lean_closure_set(x_73, 0, x_69);
lean_closure_set(x_73, 1, x_72);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_61, sizeof(void*)*7);
x_77 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 1);
x_78 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 2);
x_79 = lean_ctor_get(x_61, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_61, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_61, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 5);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 3);
x_84 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 4);
x_85 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 5);
x_86 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 7);
x_87 = lean_ctor_get(x_61, 6);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 8);
x_89 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 9);
x_90 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 10);
x_91 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 2, x_79);
lean_ctor_set(x_91, 3, x_80);
lean_ctor_set(x_91, 4, x_81);
lean_ctor_set(x_91, 5, x_82);
lean_ctor_set(x_91, 6, x_87);
lean_ctor_set_uint8(x_91, sizeof(void*)*7, x_76);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 1, x_77);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 2, x_78);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 3, x_83);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 4, x_84);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 5, x_85);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 6, x_4);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 7, x_86);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 8, x_88);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 9, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*7 + 10, x_90);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_92 = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo(lean_box(0), x_73, x_91, x_62, x_63, x_64, x_65, x_66, x_67);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
x_95 = l_Lean_Elab_Tactic_Conv_getLhs(x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_box(x_4);
x_99 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed), 11, 2);
lean_closure_set(x_99, 0, x_70);
lean_closure_set(x_99, 1, x_98);
x_100 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed), 10, 1);
lean_closure_set(x_100, 0, x_70);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 10, 1);
lean_closure_set(x_101, 0, x_70);
x_102 = lean_box(x_4);
lean_inc(x_96);
lean_inc(x_101);
lean_inc(x_5);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_93);
x_103 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__8___boxed), 20, 10);
lean_closure_set(x_103, 0, x_20);
lean_closure_set(x_103, 1, x_57);
lean_closure_set(x_103, 2, x_68);
lean_closure_set(x_103, 3, x_93);
lean_closure_set(x_103, 4, x_99);
lean_closure_set(x_103, 5, x_100);
lean_closure_set(x_103, 6, x_5);
lean_closure_set(x_103, 7, x_101);
lean_closure_set(x_103, 8, x_102);
lean_closure_set(x_103, 9, x_96);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_103);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_104 = lean_mk_empty_array_with_capacity(x_20);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_20);
lean_ctor_set(x_105, 1, x_20);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_20);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(x_20, x_57, x_68, x_93, x_99, x_100, x_5, x_101, x_4, x_96, x_108, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_97);
return x_109;
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_58);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_58, 0);
x_112 = lean_mk_string_unchecked("occsWildcard", 12, 12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_113 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_112);
lean_inc(x_111);
x_114 = l_Lean_Syntax_isOfKind(x_111, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_free_object(x_58);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_5);
x_115 = lean_mk_string_unchecked("occsIndexed", 11, 11);
x_116 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_115);
lean_inc(x_111);
x_117 = l_Lean_Syntax_isOfKind(x_111, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_111);
lean_dec(x_103);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_118 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_97);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = l_Lean_Syntax_getArg(x_111, x_20);
lean_dec(x_111);
x_124 = l_Lean_Syntax_getArgs(x_123);
lean_dec(x_123);
x_125 = lean_array_get_size(x_124);
x_126 = lean_mk_empty_array_with_capacity(x_125);
x_127 = l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(x_124, x_125, x_20, x_126, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_97);
lean_dec(x_125);
lean_dec(x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_array_get_size(x_128);
x_131 = lean_nat_dec_eq(x_130, x_20);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_nat_sub(x_130, x_57);
x_133 = lean_nat_dec_le(x_20, x_132);
if (x_133 == 0)
{
lean_inc(x_132);
x_41 = x_103;
x_42 = x_63;
x_43 = x_128;
x_44 = x_61;
x_45 = x_66;
x_46 = x_62;
x_47 = x_129;
x_48 = x_60;
x_49 = x_132;
x_50 = x_64;
x_51 = x_59;
x_52 = x_130;
x_53 = x_65;
x_54 = x_132;
goto block_56;
}
else
{
x_41 = x_103;
x_42 = x_63;
x_43 = x_128;
x_44 = x_61;
x_45 = x_66;
x_46 = x_62;
x_47 = x_129;
x_48 = x_60;
x_49 = x_132;
x_50 = x_64;
x_51 = x_59;
x_52 = x_130;
x_53 = x_65;
x_54 = x_20;
goto block_56;
}
}
else
{
lean_dec(x_130);
x_21 = x_61;
x_22 = x_66;
x_23 = x_62;
x_24 = x_129;
x_25 = x_60;
x_26 = x_64;
x_27 = x_103;
x_28 = x_59;
x_29 = x_63;
x_30 = x_65;
x_31 = x_128;
goto block_40;
}
}
else
{
uint8_t x_134; 
lean_dec(x_103);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_127);
if (x_134 == 0)
{
return x_127;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_127, 0);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_127);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_111);
lean_dec(x_103);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_138 = lean_mk_empty_array_with_capacity(x_20);
lean_ctor_set_tag(x_58, 0);
lean_ctor_set(x_58, 0, x_138);
x_139 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(x_20, x_57, x_68, x_93, x_99, x_100, x_5, x_101, x_4, x_96, x_58, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_97);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_58, 0);
lean_inc(x_140);
lean_dec(x_58);
x_141 = lean_mk_string_unchecked("occsWildcard", 12, 12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_142 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_141);
lean_inc(x_140);
x_143 = l_Lean_Syntax_isOfKind(x_140, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_5);
x_144 = lean_mk_string_unchecked("occsIndexed", 11, 11);
x_145 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_144);
lean_inc(x_140);
x_146 = l_Lean_Syntax_isOfKind(x_140, x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
lean_dec(x_103);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_147 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_97);
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
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = l_Lean_Syntax_getArg(x_140, x_20);
lean_dec(x_140);
x_153 = l_Lean_Syntax_getArgs(x_152);
lean_dec(x_152);
x_154 = lean_array_get_size(x_153);
x_155 = lean_mk_empty_array_with_capacity(x_154);
x_156 = l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(x_153, x_154, x_20, x_155, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_97);
lean_dec(x_154);
lean_dec(x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_array_get_size(x_157);
x_160 = lean_nat_dec_eq(x_159, x_20);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_nat_sub(x_159, x_57);
x_162 = lean_nat_dec_le(x_20, x_161);
if (x_162 == 0)
{
lean_inc(x_161);
x_41 = x_103;
x_42 = x_63;
x_43 = x_157;
x_44 = x_61;
x_45 = x_66;
x_46 = x_62;
x_47 = x_158;
x_48 = x_60;
x_49 = x_161;
x_50 = x_64;
x_51 = x_59;
x_52 = x_159;
x_53 = x_65;
x_54 = x_161;
goto block_56;
}
else
{
x_41 = x_103;
x_42 = x_63;
x_43 = x_157;
x_44 = x_61;
x_45 = x_66;
x_46 = x_62;
x_47 = x_158;
x_48 = x_60;
x_49 = x_161;
x_50 = x_64;
x_51 = x_59;
x_52 = x_159;
x_53 = x_65;
x_54 = x_20;
goto block_56;
}
}
else
{
lean_dec(x_159);
x_21 = x_61;
x_22 = x_66;
x_23 = x_62;
x_24 = x_158;
x_25 = x_60;
x_26 = x_64;
x_27 = x_103;
x_28 = x_59;
x_29 = x_63;
x_30 = x_65;
x_31 = x_157;
goto block_40;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_103);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_165 = x_156;
} else {
 lean_dec_ref(x_156);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_140);
lean_dec(x_103);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_167 = lean_mk_empty_array_with_capacity(x_20);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(x_20, x_57, x_68, x_93, x_99, x_100, x_5, x_101, x_4, x_96, x_168, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_97);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_93);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_95);
if (x_170 == 0)
{
return x_95;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_95, 0);
x_172 = lean_ctor_get(x_95, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_95);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_92);
if (x_174 == 0)
{
return x_92;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_92, 0);
x_176 = lean_ctor_get(x_92, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_92);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 2, 0);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("Conv", 4, 4);
x_17 = lean_mk_string_unchecked("pattern", 7, 7);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = l_Lean_Name_mkStr5(x_13, x_14, x_15, x_16, x_17);
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
lean_dec(x_18);
x_20 = lean_box(1);
x_21 = lean_box(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__9___boxed), 18, 9);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_12);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_20);
lean_closure_set(x_22, 4, x_11);
lean_closure_set(x_22, 5, x_13);
lean_closure_set(x_22, 6, x_14);
lean_closure_set(x_22, 7, x_15);
lean_closure_set(x_22, 8, x_16);
x_23 = l_Lean_Elab_Tactic_withMainContext___redArg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_Tactic_Conv_evalPattern_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Lean_Elab_Tactic_Conv_evalPattern_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Conv_evalPattern_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__8___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__9___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_1);
lean_dec(x_1);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = l_Lean_Elab_Tactic_Conv_evalPattern___lam__9(x_19, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("pattern", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalPattern", 11, 11);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("Conv", 4, 4);
x_6 = lean_mk_string_unchecked("evalPattern", 11, 11);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(105u);
x_9 = lean_unsigned_to_nat(50u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(142u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(54u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(65u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
