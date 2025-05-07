// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Lookahead
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.Arith Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.EMatch
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
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ematchAndAssert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_withoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_mk_string_unchecked("`grind` lookahead internal error, unexpected number of goals", 60, 60);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg(x_16, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("runtime", 7, 7);
x_4 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_10, x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 9);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_26 = lean_ctor_get(x_7, 11);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_7, 12);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_18);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_11);
lean_ctor_set(x_29, 5, x_19);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set(x_29, 12, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*13 + 1, x_27);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Meta_Grind_assertNext(x_1, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Meta_Grind_Arith_check(x_1, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Meta_Grind_splitNext(x_1, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Meta_Grind_ematchAndAssert(x_1, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(x_12);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(x_12);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(x_48, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_dec(x_36);
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
lean_dec(x_37);
x_56 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(x_55, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_36);
if (x_57 == 0)
{
return x_36;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_36, 0);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_36);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 0);
lean_inc(x_62);
lean_dec(x_34);
x_63 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(x_62, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_33);
if (x_64 == 0)
{
return x_33;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_33, 0);
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_33);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_68 = lean_ctor_get(x_30, 1);
lean_inc(x_68);
lean_dec(x_30);
x_69 = lean_ctor_get(x_31, 0);
lean_inc(x_69);
lean_dec(x_31);
x_70 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(x_69, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
return x_30;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_30, 0);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
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
x_75 = lean_box(x_13);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_9);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_7, 5);
lean_inc(x_77);
lean_dec(x_7);
x_78 = l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_77, x_9);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_____private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_Grind_intros(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_cont(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Lean_MVarId_getTag(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_getFalseExpr(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = l_Lean_mkNot(x_1);
x_22 = l_Lean_mkArrow(x_21, x_19, x_8, x_9, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_box(2);
x_27 = lean_unbox(x_26);
lean_inc(x_6);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_25, x_27, x_16, x_6, x_7, x_8, x_9, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_30);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_mvarId_x21(x_29);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_12, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_12, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_12, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_12, 7);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_12, sizeof(void*)*16);
x_43 = lean_ctor_get(x_12, 8);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 9);
lean_inc(x_44);
x_45 = lean_ctor_get(x_12, 10);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 11);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 12);
lean_inc(x_47);
x_48 = lean_ctor_get(x_12, 13);
lean_inc(x_48);
x_49 = lean_ctor_get(x_12, 14);
lean_inc(x_49);
x_50 = lean_ctor_get(x_12, 15);
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_35);
lean_ctor_set(x_51, 2, x_36);
lean_ctor_set(x_51, 3, x_37);
lean_ctor_set(x_51, 4, x_38);
lean_ctor_set(x_51, 5, x_39);
lean_ctor_set(x_51, 6, x_40);
lean_ctor_set(x_51, 7, x_41);
lean_ctor_set(x_51, 8, x_43);
lean_ctor_set(x_51, 9, x_44);
lean_ctor_set(x_51, 10, x_45);
lean_ctor_set(x_51, 11, x_46);
lean_ctor_set(x_51, 12, x_47);
lean_ctor_set(x_51, 13, x_48);
lean_ctor_set(x_51, 14, x_49);
lean_ctor_set(x_51, 15, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*16, x_42);
lean_inc(x_7);
x_52 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(x_32, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_29, x_7, x_61);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_29);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_52);
if (x_70 == 0)
{
return x_52;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_52, 0);
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_52);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_15);
if (x_74 == 0)
{
return x_15;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_15, 0);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_15);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_102; 
x_46 = lean_mk_string_unchecked("grind", 5, 5);
x_47 = lean_mk_string_unchecked("lookahead", 9, 9);
x_48 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_47);
lean_inc(x_46);
x_49 = l_Lean_Name_mkStr3(x_46, x_47, x_48);
lean_inc(x_49);
x_50 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_49, x_8, x_10);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
lean_inc(x_1);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 10, 1);
lean_closure_set(x_54, 0, x_1);
x_102 = lean_unbox(x_51);
lean_dec(x_51);
if (x_102 == 0)
{
lean_dec(x_49);
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_52;
goto block_101;
}
else
{
lean_object* x_103; 
x_103 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
lean_inc(x_1);
x_107 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
x_110 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_49, x_109, x_6, x_7, x_8, x_9, x_104);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_111;
goto block_101;
}
else
{
uint8_t x_112; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_103);
if (x_112 == 0)
{
return x_103;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_103, 0);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_103);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Grind", 5, 5);
x_23 = lean_mk_string_unchecked("of_lookahead", 12, 12);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_24, x_25);
lean_inc(x_1);
x_27 = l_Lean_mkAppB(x_26, x_1, x_11);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_28 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_27, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_grind_process_new_facts(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(1);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_101:
{
lean_object* x_64; 
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_64 = l_Lean_Meta_Grind_withoutModifyingState(lean_box(0), x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_mk_string_unchecked("assert", 6, 6);
x_75 = l_Lean_Name_mkStr3(x_46, x_47, x_74);
lean_inc(x_75);
x_76 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_75, x_61, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_53);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_11 = x_73;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = x_79;
goto block_45;
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_76, 1);
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
lean_inc(x_1);
x_85 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_84);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_85);
lean_ctor_set(x_76, 0, x_84);
if (lean_is_scalar(x_53)) {
 x_86 = lean_alloc_ctor(7, 2, 0);
} else {
 x_86 = x_53;
 lean_ctor_set_tag(x_86, 7);
}
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_75, x_86, x_59, x_60, x_61, x_62, x_81);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_11 = x_73;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = x_88;
goto block_45;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
lean_dec(x_76);
x_90 = lean_mk_string_unchecked("", 0, 0);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_inc(x_1);
x_92 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_53)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_53;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_95 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_75, x_94, x_59, x_60, x_61, x_62, x_89);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_11 = x_73;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = x_96;
goto block_45;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_64);
if (x_97 == 0)
{
return x_64;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_64, 0);
x_99 = lean_ctor_get(x_64, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_64);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 1);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 2);
x_21 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 3);
x_22 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 4);
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 5);
x_24 = lean_ctor_get(x_13, 4);
x_25 = lean_ctor_get(x_13, 5);
x_26 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 6);
x_27 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 7);
x_28 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_29 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_31 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 11);
x_32 = lean_box(1);
x_33 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 13);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 14);
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 15);
x_36 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 16);
x_37 = lean_ctor_get(x_13, 6);
x_38 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 17);
lean_inc(x_37);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_39 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_18);
lean_ctor_set(x_39, 4, x_24);
lean_ctor_set(x_39, 5, x_25);
lean_ctor_set(x_39, 6, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_19);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 2, x_20);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 3, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 4, x_22);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 5, x_23);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 6, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 7, x_27);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 8, x_28);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 9, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 10, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 11, x_31);
x_40 = lean_unbox(x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 12, x_40);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 13, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 14, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 15, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 16, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 17, x_38);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_11);
lean_ctor_set(x_42, 2, x_12);
lean_ctor_set(x_42, 3, x_39);
x_43 = lean_unbox(x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_43);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 1, x_41);
x_44 = lean_apply_8(x_1, x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_24 = l_Lean_Meta_Grind_checkSplitStatus(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_free_object(x_2);
lean_dec(x_15);
x_28 = lean_box(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_2 = x_16;
x_3 = x_30;
x_12 = x_26;
goto _start;
}
case 1:
{
lean_object* x_32; lean_object* x_33; 
lean_ctor_set(x_2, 1, x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_2 = x_16;
x_3 = x_33;
x_12 = x_26;
goto _start;
}
default: 
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_25, sizeof(void*)*1 + 1);
lean_dec(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_2, 1, x_22);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_23);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_16;
x_3 = x_42;
x_12 = x_40;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_23);
lean_free_object(x_2);
lean_dec(x_15);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_45);
x_2 = x_16;
x_3 = x_46;
x_12 = x_44;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_ctor_set(x_2, 1, x_22);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_23);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_52);
x_2 = x_16;
x_3 = x_53;
x_12 = x_26;
goto _start;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_17, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_3, 1);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_box(x_1);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_17, 0, x_67);
return x_17;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_17, 1);
lean_inc(x_68);
lean_dec(x_17);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(x_1);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_2);
x_79 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4, x_12);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_3, 1);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_77);
x_86 = l_Lean_Meta_Grind_checkSplitStatus(x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_dec(x_77);
x_90 = lean_box(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_2 = x_78;
x_3 = x_92;
x_12 = x_88;
goto _start;
}
case 1:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_94, 1, x_84);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_85);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_95);
x_2 = x_78;
x_3 = x_96;
x_12 = x_88;
goto _start;
}
default: 
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_87, sizeof(void*)*1 + 1);
lean_dec(x_87);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_77);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_100 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_99, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_88);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_101);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_77);
lean_ctor_set(x_104, 1, x_84);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_85);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_89);
lean_ctor_set(x_106, 1, x_105);
x_2 = x_78;
x_3 = x_106;
x_12 = x_103;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_85);
lean_dec(x_77);
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
lean_dec(x_100);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_84);
lean_ctor_set(x_109, 1, x_101);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_109);
x_2 = x_78;
x_3 = x_110;
x_12 = x_108;
goto _start;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_114 = x_100;
} else {
 lean_dec_ref(x_100);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_77);
lean_ctor_set(x_116, 1, x_84);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_85);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_89);
lean_ctor_set(x_118, 1, x_117);
x_2 = x_78;
x_3 = x_118;
x_12 = x_88;
goto _start;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_ctor_get(x_86, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_122 = x_86;
} else {
 lean_dec_ref(x_86);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_125 = x_79;
} else {
 lean_dec_ref(x_79);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_3, 1);
lean_inc(x_126);
lean_dec(x_3);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_box(x_1);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_128);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
if (lean_is_scalar(x_125)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_125;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_124);
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_13 = lean_st_mk_ref(x_1, x_12);
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
x_30 = lean_st_ref_get(x_14, x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_14, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 7);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_35, sizeof(void*)*16);
x_46 = lean_ctor_get(x_35, 8);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 9);
lean_inc(x_47);
x_48 = lean_ctor_get(x_35, 10);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 11);
lean_inc(x_49);
x_50 = lean_ctor_get(x_35, 12);
lean_inc(x_50);
x_51 = lean_ctor_get(x_35, 13);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 7);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 8);
lean_inc(x_59);
lean_dec(x_51);
lean_inc(x_2);
x_60 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_2);
lean_ctor_set(x_60, 7, x_58);
lean_ctor_set(x_60, 8, x_59);
x_61 = lean_ctor_get(x_35, 14);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 15);
lean_inc(x_62);
lean_dec(x_35);
x_63 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_38);
lean_ctor_set(x_63, 2, x_39);
lean_ctor_set(x_63, 3, x_40);
lean_ctor_set(x_63, 4, x_41);
lean_ctor_set(x_63, 5, x_42);
lean_ctor_set(x_63, 6, x_43);
lean_ctor_set(x_63, 7, x_44);
lean_ctor_set(x_63, 8, x_46);
lean_ctor_set(x_63, 9, x_47);
lean_ctor_set(x_63, 10, x_48);
lean_ctor_set(x_63, 11, x_49);
lean_ctor_set(x_63, 12, x_50);
lean_ctor_set(x_63, 13, x_60);
lean_ctor_set(x_63, 14, x_61);
lean_ctor_set(x_63, 15, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*16, x_45);
x_64 = lean_st_ref_set(x_14, x_63, x_36);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_31, 13);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_ctor_get(x_68, 6);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = lean_box(x_3);
lean_ctor_set(x_64, 1, x_71);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_33, 1, x_64);
lean_ctor_set(x_33, 0, x_70);
lean_inc(x_14);
x_72 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(x_4, x_69, x_33, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_17 = x_3;
x_18 = x_78;
goto block_29;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_st_ref_take(x_14, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 5);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 6);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 7);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_82, sizeof(void*)*16);
x_93 = lean_ctor_get(x_82, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 11);
lean_inc(x_96);
x_97 = lean_ctor_get(x_82, 12);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 13);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 6);
lean_inc(x_105);
x_106 = l_List_reverse___redArg(x_80);
x_107 = l_List_appendTR(lean_box(0), x_105, x_106);
x_108 = lean_ctor_get(x_98, 7);
lean_inc(x_108);
x_109 = lean_ctor_get(x_98, 8);
lean_inc(x_109);
lean_dec(x_98);
x_110 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
lean_ctor_set(x_110, 6, x_107);
lean_ctor_set(x_110, 7, x_108);
lean_ctor_set(x_110, 8, x_109);
x_111 = lean_ctor_get(x_82, 14);
lean_inc(x_111);
x_112 = lean_ctor_get(x_82, 15);
lean_inc(x_112);
lean_dec(x_82);
x_113 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_113, 0, x_84);
lean_ctor_set(x_113, 1, x_85);
lean_ctor_set(x_113, 2, x_86);
lean_ctor_set(x_113, 3, x_87);
lean_ctor_set(x_113, 4, x_88);
lean_ctor_set(x_113, 5, x_89);
lean_ctor_set(x_113, 6, x_90);
lean_ctor_set(x_113, 7, x_91);
lean_ctor_set(x_113, 8, x_93);
lean_ctor_set(x_113, 9, x_94);
lean_ctor_set(x_113, 10, x_95);
lean_ctor_set(x_113, 11, x_96);
lean_ctor_set(x_113, 12, x_97);
lean_ctor_set(x_113, 13, x_110);
lean_ctor_set(x_113, 14, x_111);
lean_ctor_set(x_113, 15, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*16, x_92);
x_114 = lean_st_ref_set(x_14, x_113, x_83);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_17 = x_4;
x_18 = x_115;
goto block_29;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_74);
x_116 = lean_ctor_get(x_72, 1);
lean_inc(x_116);
lean_dec(x_72);
x_117 = lean_ctor_get(x_75, 0);
lean_inc(x_117);
lean_dec(x_75);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
x_17 = x_118;
x_18 = x_116;
goto block_29;
}
}
else
{
uint8_t x_119; 
lean_dec(x_16);
lean_dec(x_14);
x_119 = !lean_is_exclusive(x_72);
if (x_119 == 0)
{
return x_72;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_72, 0);
x_121 = lean_ctor_get(x_72, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_72);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_64, 1);
lean_inc(x_123);
lean_dec(x_64);
x_124 = lean_ctor_get(x_31, 13);
lean_inc(x_124);
lean_dec(x_31);
x_125 = lean_ctor_get(x_124, 6);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_box(0);
x_127 = lean_box(x_3);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_2);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_33, 1, x_128);
lean_ctor_set(x_33, 0, x_126);
lean_inc(x_14);
x_129 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(x_4, x_125, x_33, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_123);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_131);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_dec(x_129);
x_17 = x_3;
x_18 = x_135;
goto block_29;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
lean_dec(x_131);
x_138 = lean_st_ref_take(x_14, x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_139, 5);
lean_inc(x_146);
x_147 = lean_ctor_get(x_139, 6);
lean_inc(x_147);
x_148 = lean_ctor_get(x_139, 7);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_139, sizeof(void*)*16);
x_150 = lean_ctor_get(x_139, 8);
lean_inc(x_150);
x_151 = lean_ctor_get(x_139, 9);
lean_inc(x_151);
x_152 = lean_ctor_get(x_139, 10);
lean_inc(x_152);
x_153 = lean_ctor_get(x_139, 11);
lean_inc(x_153);
x_154 = lean_ctor_get(x_139, 12);
lean_inc(x_154);
x_155 = lean_ctor_get(x_139, 13);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_155, 6);
lean_inc(x_162);
x_163 = l_List_reverse___redArg(x_137);
x_164 = l_List_appendTR(lean_box(0), x_162, x_163);
x_165 = lean_ctor_get(x_155, 7);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 8);
lean_inc(x_166);
lean_dec(x_155);
x_167 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_157);
lean_ctor_set(x_167, 2, x_158);
lean_ctor_set(x_167, 3, x_159);
lean_ctor_set(x_167, 4, x_160);
lean_ctor_set(x_167, 5, x_161);
lean_ctor_set(x_167, 6, x_164);
lean_ctor_set(x_167, 7, x_165);
lean_ctor_set(x_167, 8, x_166);
x_168 = lean_ctor_get(x_139, 14);
lean_inc(x_168);
x_169 = lean_ctor_get(x_139, 15);
lean_inc(x_169);
lean_dec(x_139);
x_170 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_170, 0, x_141);
lean_ctor_set(x_170, 1, x_142);
lean_ctor_set(x_170, 2, x_143);
lean_ctor_set(x_170, 3, x_144);
lean_ctor_set(x_170, 4, x_145);
lean_ctor_set(x_170, 5, x_146);
lean_ctor_set(x_170, 6, x_147);
lean_ctor_set(x_170, 7, x_148);
lean_ctor_set(x_170, 8, x_150);
lean_ctor_set(x_170, 9, x_151);
lean_ctor_set(x_170, 10, x_152);
lean_ctor_set(x_170, 11, x_153);
lean_ctor_set(x_170, 12, x_154);
lean_ctor_set(x_170, 13, x_167);
lean_ctor_set(x_170, 14, x_168);
lean_ctor_set(x_170, 15, x_169);
lean_ctor_set_uint8(x_170, sizeof(void*)*16, x_149);
x_171 = lean_st_ref_set(x_14, x_170, x_140);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_17 = x_4;
x_18 = x_172;
goto block_29;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_131);
x_173 = lean_ctor_get(x_129, 1);
lean_inc(x_173);
lean_dec(x_129);
x_174 = lean_ctor_get(x_132, 0);
lean_inc(x_174);
lean_dec(x_132);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
x_17 = x_175;
x_18 = x_173;
goto block_29;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_16);
lean_dec(x_14);
x_176 = lean_ctor_get(x_129, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_129, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_178 = x_129;
} else {
 lean_dec_ref(x_129);
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
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_180 = lean_ctor_get(x_33, 0);
x_181 = lean_ctor_get(x_33, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_33);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 5);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 6);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 7);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_180, sizeof(void*)*16);
x_191 = lean_ctor_get(x_180, 8);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 9);
lean_inc(x_192);
x_193 = lean_ctor_get(x_180, 10);
lean_inc(x_193);
x_194 = lean_ctor_get(x_180, 11);
lean_inc(x_194);
x_195 = lean_ctor_get(x_180, 12);
lean_inc(x_195);
x_196 = lean_ctor_get(x_180, 13);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_196, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 7);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 8);
lean_inc(x_204);
lean_dec(x_196);
lean_inc(x_2);
x_205 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_205, 0, x_197);
lean_ctor_set(x_205, 1, x_198);
lean_ctor_set(x_205, 2, x_199);
lean_ctor_set(x_205, 3, x_200);
lean_ctor_set(x_205, 4, x_201);
lean_ctor_set(x_205, 5, x_202);
lean_ctor_set(x_205, 6, x_2);
lean_ctor_set(x_205, 7, x_203);
lean_ctor_set(x_205, 8, x_204);
x_206 = lean_ctor_get(x_180, 14);
lean_inc(x_206);
x_207 = lean_ctor_get(x_180, 15);
lean_inc(x_207);
lean_dec(x_180);
x_208 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_208, 0, x_182);
lean_ctor_set(x_208, 1, x_183);
lean_ctor_set(x_208, 2, x_184);
lean_ctor_set(x_208, 3, x_185);
lean_ctor_set(x_208, 4, x_186);
lean_ctor_set(x_208, 5, x_187);
lean_ctor_set(x_208, 6, x_188);
lean_ctor_set(x_208, 7, x_189);
lean_ctor_set(x_208, 8, x_191);
lean_ctor_set(x_208, 9, x_192);
lean_ctor_set(x_208, 10, x_193);
lean_ctor_set(x_208, 11, x_194);
lean_ctor_set(x_208, 12, x_195);
lean_ctor_set(x_208, 13, x_205);
lean_ctor_set(x_208, 14, x_206);
lean_ctor_set(x_208, 15, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*16, x_190);
x_209 = lean_st_ref_set(x_14, x_208, x_181);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_31, 13);
lean_inc(x_212);
lean_dec(x_31);
x_213 = lean_ctor_get(x_212, 6);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_box(0);
x_215 = lean_box(x_3);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_2);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_14);
x_218 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(x_4, x_213, x_217, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_210);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_220);
x_224 = lean_ctor_get(x_218, 1);
lean_inc(x_224);
lean_dec(x_218);
x_17 = x_3;
x_18 = x_224;
goto block_29;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
lean_dec(x_218);
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
lean_dec(x_220);
x_227 = lean_st_ref_take(x_14, x_225);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_228, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_228, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_228, 4);
lean_inc(x_234);
x_235 = lean_ctor_get(x_228, 5);
lean_inc(x_235);
x_236 = lean_ctor_get(x_228, 6);
lean_inc(x_236);
x_237 = lean_ctor_get(x_228, 7);
lean_inc(x_237);
x_238 = lean_ctor_get_uint8(x_228, sizeof(void*)*16);
x_239 = lean_ctor_get(x_228, 8);
lean_inc(x_239);
x_240 = lean_ctor_get(x_228, 9);
lean_inc(x_240);
x_241 = lean_ctor_get(x_228, 10);
lean_inc(x_241);
x_242 = lean_ctor_get(x_228, 11);
lean_inc(x_242);
x_243 = lean_ctor_get(x_228, 12);
lean_inc(x_243);
x_244 = lean_ctor_get(x_228, 13);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_244, 3);
lean_inc(x_248);
x_249 = lean_ctor_get(x_244, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 5);
lean_inc(x_250);
x_251 = lean_ctor_get(x_244, 6);
lean_inc(x_251);
x_252 = l_List_reverse___redArg(x_226);
x_253 = l_List_appendTR(lean_box(0), x_251, x_252);
x_254 = lean_ctor_get(x_244, 7);
lean_inc(x_254);
x_255 = lean_ctor_get(x_244, 8);
lean_inc(x_255);
lean_dec(x_244);
x_256 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_256, 0, x_245);
lean_ctor_set(x_256, 1, x_246);
lean_ctor_set(x_256, 2, x_247);
lean_ctor_set(x_256, 3, x_248);
lean_ctor_set(x_256, 4, x_249);
lean_ctor_set(x_256, 5, x_250);
lean_ctor_set(x_256, 6, x_253);
lean_ctor_set(x_256, 7, x_254);
lean_ctor_set(x_256, 8, x_255);
x_257 = lean_ctor_get(x_228, 14);
lean_inc(x_257);
x_258 = lean_ctor_get(x_228, 15);
lean_inc(x_258);
lean_dec(x_228);
x_259 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_259, 0, x_230);
lean_ctor_set(x_259, 1, x_231);
lean_ctor_set(x_259, 2, x_232);
lean_ctor_set(x_259, 3, x_233);
lean_ctor_set(x_259, 4, x_234);
lean_ctor_set(x_259, 5, x_235);
lean_ctor_set(x_259, 6, x_236);
lean_ctor_set(x_259, 7, x_237);
lean_ctor_set(x_259, 8, x_239);
lean_ctor_set(x_259, 9, x_240);
lean_ctor_set(x_259, 10, x_241);
lean_ctor_set(x_259, 11, x_242);
lean_ctor_set(x_259, 12, x_243);
lean_ctor_set(x_259, 13, x_256);
lean_ctor_set(x_259, 14, x_257);
lean_ctor_set(x_259, 15, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*16, x_238);
x_260 = lean_st_ref_set(x_14, x_259, x_229);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_17 = x_4;
x_18 = x_261;
goto block_29;
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
lean_dec(x_220);
x_262 = lean_ctor_get(x_218, 1);
lean_inc(x_262);
lean_dec(x_218);
x_263 = lean_ctor_get(x_221, 0);
lean_inc(x_263);
lean_dec(x_221);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
x_17 = x_264;
x_18 = x_262;
goto block_29;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_16);
lean_dec(x_14);
x_265 = lean_ctor_get(x_218, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_218, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_267 = x_218;
} else {
 lean_dec_ref(x_218);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
block_29:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_box(x_17);
if (lean_is_scalar(x_16)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_16;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_box(x_17);
if (lean_is_scalar(x_16)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_16;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_35 = x_13;
} else {
 lean_dec_ref(x_13);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_35;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 13);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 6);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_isEmpty___redArg(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
x_25 = lean_box(0);
x_26 = lean_box(x_24);
x_27 = lean_box(x_12);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_lookahead___lam__0___boxed), 12, 4);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_lookahead___lam__1___boxed), 10, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_ctor_get(x_1, 13);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 6);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_List_isEmpty___redArg(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_box(0);
x_37 = lean_box(x_35);
x_38 = lean_box(x_12);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_lookahead___lam__0___boxed), 12, 4);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_36);
lean_closure_set(x_39, 2, x_37);
lean_closure_set(x_39, 3, x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_lookahead___lam__1___boxed), 10, 2);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_withLookaheadConfig___redArg(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_lookahead_spec__0(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_Grind_lookahead___lam__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_lookahead___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_lookahead(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
