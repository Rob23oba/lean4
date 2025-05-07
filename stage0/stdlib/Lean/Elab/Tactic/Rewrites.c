// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrites
// Imports: Lean.Elab.Tactic.Location Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Rewrites
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object**);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Rewrites_evalExact__1(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4(size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object**);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reportOutOfHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_getBracketedBinderIds_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__List_get_x3fInternal(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
lean_inc(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(x_18, x_15, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_16;
x_12 = x_21;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_10, x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_10, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_20 = lean_box(x_19);
lean_inc(x_18);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Expr_fvar___override(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_30 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_3, x_22, x_25, x_27, x_28, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_ctor_get(x_10, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_36 = lean_box(x_35);
lean_inc(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Expr_fvar___override(x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_33);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_31);
x_47 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_3, x_39, x_42, x_44, x_45, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_45);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
lean_inc(x_1);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_ctor_get(x_15, 3);
lean_inc(x_20);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_box(0), x_20, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_3 = x_16;
x_4 = x_23;
x_13 = x_22;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
lean_inc(x_1);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_box(0), x_21, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg(x_1, x_2, x_17, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
return x_25;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_NameSet_insert(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_mk_string_unchecked("group", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_6);
x_9 = l_Lean_Syntax_isOfKind(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_uset(x_3, x_2, x_11);
x_14 = l_Lean_Syntax_getArg(x_6, x_12);
lean_dec(x_6);
x_15 = lean_usize_of_nat(x_12);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Tactic", 6, 6);
x_17 = lean_mk_string_unchecked("rewrites_forbidden", 18, 18);
x_18 = lean_usize_dec_eq(x_3, x_4);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = l_Lean_Syntax_getArg(x_1, x_12);
x_23 = lean_unbox(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_22);
x_25 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
lean_ctor_set(x_5, 0, x_27);
x_6 = x_5;
goto block_11;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_28 = l_Lean_Syntax_isNone(x_22);
lean_dec(x_22);
x_29 = lean_array_uget(x_2, x_3);
x_30 = lean_array_push(x_21, x_29);
x_31 = lean_box(x_28);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_31);
x_6 = x_5;
goto block_11;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = l_Lean_Syntax_getArg(x_1, x_12);
x_35 = lean_unbox(x_32);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_Syntax_getArg(x_34, x_13);
lean_dec(x_34);
x_37 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_38 = l_Lean_Syntax_isOfKind(x_36, x_37);
lean_dec(x_37);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
x_6 = x_40;
goto block_11;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_41 = l_Lean_Syntax_isNone(x_34);
lean_dec(x_34);
x_42 = lean_array_uget(x_2, x_3);
x_43 = lean_array_push(x_33, x_42);
x_44 = lean_box(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_6 = x_45;
goto block_11;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_mk_string_unchecked("Failed to find a rewrite for some location", 42, 42);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_13);
lean_inc(x_8);
x_18 = l_Lean_FVarId_findDecl_x3f___redArg(x_8, x_13, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
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
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_18, 1);
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lean_LocalDecl_isImplementationDetail(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_18);
lean_inc(x_13);
lean_inc(x_8);
x_31 = l_Lean_FVarId_getType___redArg(x_8, x_13, x_15, x_16, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_32, x_14, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_box(0);
lean_inc(x_8);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_38);
lean_ctor_set(x_34, 0, x_8);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_39 = l_Lean_Meta_Rewrites_localHypotheses(x_34, x_13, x_14, x_15, x_16, x_37);
lean_dec(x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(2);
x_43 = lean_unsigned_to_nat(20u);
x_44 = lean_unsigned_to_nat(10u);
x_45 = lean_unbox(x_42);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_46 = l_Lean_Meta_Rewrites_findRewrites(x_40, x_1, x_2, x_36, x_3, x_45, x_30, x_43, x_44, x_13, x_14, x_15, x_16, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_mk_string_unchecked("rewrites", 8, 8);
x_50 = l_Lean_Name_mkStr1(x_49);
lean_inc(x_15);
x_51 = l_Lean_reportOutOfHeartbeats(x_50, x_4, x_5, x_15, x_16, x_48);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = l_List_isEmpty___redArg(x_47);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_51);
x_56 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_47);
lean_inc(x_8);
x_57 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_8, x_6, x_47, x_47, x_56, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_53);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_47, x_7);
lean_dec(x_47);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_free_object(x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_14, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_62, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 4);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
x_72 = lean_st_ref_set(x_14, x_71, x_65);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_72, 1);
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_62, 2);
lean_inc(x_76);
lean_dec(x_62);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_79 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_77, x_78, x_13, x_14, x_15, x_16, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_76, 2);
lean_inc(x_83);
lean_dec(x_76);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_83);
lean_ctor_set(x_72, 0, x_82);
x_84 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_72, x_10, x_13, x_14, x_15, x_16, x_81);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_76);
lean_free_object(x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_85 = !lean_is_exclusive(x_79);
if (x_85 == 0)
{
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_90 = lean_ctor_get(x_62, 2);
lean_inc(x_90);
lean_dec(x_62);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_93 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_91, x_92, x_13, x_14, x_15, x_16, x_89);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_90, 2);
lean_inc(x_97);
lean_dec(x_90);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_98, x_10, x_13, x_14, x_15, x_16, x_95);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_57, 1);
lean_inc(x_104);
lean_dec(x_57);
x_105 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_47, x_7);
lean_dec(x_47);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_56);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_14, x_104);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 4);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 4, x_115);
x_117 = lean_st_ref_set(x_14, x_116, x_110);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_107, 2);
lean_inc(x_120);
lean_dec(x_107);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_123 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_121, x_122, x_13, x_14, x_15, x_16, x_118);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_120, 2);
lean_inc(x_127);
lean_dec(x_120);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_119;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_128, x_10, x_13, x_14, x_15, x_16, x_125);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
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
}
else
{
lean_dec(x_47);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_57;
}
}
else
{
lean_object* x_134; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_13);
x_134 = l_Lean_FVarId_getUserName(x_8, x_13, x_14, x_15, x_16, x_53);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the hypothesis ", 59, 59);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = l_Lean_MessageData_ofName(x_135);
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_139);
lean_ctor_set(x_51, 0, x_138);
x_140 = lean_mk_string_unchecked("", 0, 0);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_51);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_142, x_13, x_14, x_15, x_16, x_136);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_143;
}
else
{
uint8_t x_144; 
lean_free_object(x_51);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_144 = !lean_is_exclusive(x_134);
if (x_144 == 0)
{
return x_134;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_134, 0);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_134);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_51, 1);
lean_inc(x_148);
lean_dec(x_51);
x_149 = l_List_isEmpty___redArg(x_47);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_47);
lean_inc(x_8);
x_151 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_8, x_6, x_47, x_47, x_150, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_47, x_7);
lean_dec(x_47);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_st_ref_take(x_14, x_152);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_156, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 4);
lean_inc(x_164);
lean_dec(x_158);
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set(x_165, 2, x_162);
lean_ctor_set(x_165, 3, x_163);
lean_ctor_set(x_165, 4, x_164);
x_166 = lean_st_ref_set(x_14, x_165, x_159);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_156, 2);
lean_inc(x_169);
lean_dec(x_156);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_172 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_170, x_171, x_13, x_14, x_15, x_16, x_167);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_169, 2);
lean_inc(x_176);
lean_dec(x_169);
if (lean_is_scalar(x_168)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_168;
 lean_ctor_set_tag(x_177, 1);
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_177, x_10, x_13, x_14, x_15, x_16, x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_dec(x_47);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_151;
}
}
else
{
lean_object* x_183; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_13);
x_183 = l_Lean_FVarId_getUserName(x_8, x_13, x_14, x_15, x_16, x_148);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the hypothesis ", 59, 59);
x_187 = l_Lean_stringToMessageData(x_186);
lean_dec(x_186);
x_188 = l_Lean_MessageData_ofName(x_184);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_mk_string_unchecked("", 0, 0);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_192, x_13, x_14, x_15, x_16, x_185);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_194 = lean_ctor_get(x_183, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_196 = x_183;
} else {
 lean_dec_ref(x_183);
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
}
}
else
{
uint8_t x_198; 
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
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_46);
if (x_198 == 0)
{
return x_46;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_46, 0);
x_200 = lean_ctor_get(x_46, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_46);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_36);
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
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_39);
if (x_202 == 0)
{
return x_39;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_39, 0);
x_204 = lean_ctor_get(x_39, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_39);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_34, 0);
x_207 = lean_ctor_get(x_34, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_34);
x_208 = lean_box(0);
lean_inc(x_8);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_8);
lean_ctor_set(x_209, 1, x_208);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_210 = l_Lean_Meta_Rewrites_localHypotheses(x_209, x_13, x_14, x_15, x_16, x_207);
lean_dec(x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_box(2);
x_214 = lean_unsigned_to_nat(20u);
x_215 = lean_unsigned_to_nat(10u);
x_216 = lean_unbox(x_213);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_217 = l_Lean_Meta_Rewrites_findRewrites(x_211, x_1, x_2, x_206, x_3, x_216, x_30, x_214, x_215, x_13, x_14, x_15, x_16, x_212);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_mk_string_unchecked("rewrites", 8, 8);
x_221 = l_Lean_Name_mkStr1(x_220);
lean_inc(x_15);
x_222 = l_Lean_reportOutOfHeartbeats(x_221, x_4, x_5, x_15, x_16, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = l_List_isEmpty___redArg(x_218);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_224);
x_226 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_218);
lean_inc(x_8);
x_227 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_8, x_6, x_218, x_218, x_226, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_223);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_218, x_7);
lean_dec(x_218);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_226);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_ref_take(x_14, x_228);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_232, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 4);
lean_inc(x_240);
lean_dec(x_234);
x_241 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_241, 0, x_236);
lean_ctor_set(x_241, 1, x_237);
lean_ctor_set(x_241, 2, x_238);
lean_ctor_set(x_241, 3, x_239);
lean_ctor_set(x_241, 4, x_240);
x_242 = lean_st_ref_set(x_14, x_241, x_235);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_232, 2);
lean_inc(x_245);
lean_dec(x_232);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_248 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_246, x_247, x_13, x_14, x_15, x_16, x_243);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_245, 2);
lean_inc(x_252);
lean_dec(x_245);
if (lean_is_scalar(x_244)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_244;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_253, x_10, x_13, x_14, x_15, x_16, x_250);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_257 = x_248;
} else {
 lean_dec_ref(x_248);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
else
{
lean_dec(x_218);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_227;
}
}
else
{
lean_object* x_259; 
lean_dec(x_218);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_13);
x_259 = l_Lean_FVarId_getUserName(x_8, x_13, x_14, x_15, x_16, x_223);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the hypothesis ", 59, 59);
x_263 = l_Lean_stringToMessageData(x_262);
lean_dec(x_262);
x_264 = l_Lean_MessageData_ofName(x_260);
if (lean_is_scalar(x_224)) {
 x_265 = lean_alloc_ctor(7, 2, 0);
} else {
 x_265 = x_224;
 lean_ctor_set_tag(x_265, 7);
}
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_mk_string_unchecked("", 0, 0);
x_267 = l_Lean_stringToMessageData(x_266);
lean_dec(x_266);
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_268, x_13, x_14, x_15, x_16, x_261);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_224);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_270 = lean_ctor_get(x_259, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_259, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_272 = x_259;
} else {
 lean_dec_ref(x_259);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
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
lean_dec(x_2);
x_274 = lean_ctor_get(x_217, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_217, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_276 = x_217;
} else {
 lean_dec_ref(x_217);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_206);
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
lean_dec(x_2);
lean_dec(x_1);
x_278 = lean_ctor_get(x_210, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_210, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_280 = x_210;
} else {
 lean_dec_ref(x_210);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
else
{
uint8_t x_282; 
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
lean_dec(x_2);
lean_dec(x_1);
x_282 = !lean_is_exclusive(x_31);
if (x_282 == 0)
{
return x_31;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_31, 0);
x_284 = lean_ctor_get(x_31, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_31);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; 
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
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_box(0);
lean_ctor_set(x_18, 0, x_286);
return x_18;
}
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_287 = lean_ctor_get(x_18, 1);
lean_inc(x_287);
lean_dec(x_18);
x_288 = lean_ctor_get(x_19, 0);
lean_inc(x_288);
lean_dec(x_19);
x_289 = l_Lean_LocalDecl_isImplementationDetail(x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_inc(x_13);
lean_inc(x_8);
x_290 = l_Lean_FVarId_getType___redArg(x_8, x_13, x_15, x_16, x_287);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_291, x_14, x_292);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = lean_box(0);
lean_inc(x_8);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_296;
 lean_ctor_set_tag(x_298, 1);
}
lean_ctor_set(x_298, 0, x_8);
lean_ctor_set(x_298, 1, x_297);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_299 = l_Lean_Meta_Rewrites_localHypotheses(x_298, x_13, x_14, x_15, x_16, x_295);
lean_dec(x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_box(2);
x_303 = lean_unsigned_to_nat(20u);
x_304 = lean_unsigned_to_nat(10u);
x_305 = lean_unbox(x_302);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_306 = l_Lean_Meta_Rewrites_findRewrites(x_300, x_1, x_2, x_294, x_3, x_305, x_289, x_303, x_304, x_13, x_14, x_15, x_16, x_301);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_mk_string_unchecked("rewrites", 8, 8);
x_310 = l_Lean_Name_mkStr1(x_309);
lean_inc(x_15);
x_311 = l_Lean_reportOutOfHeartbeats(x_310, x_4, x_5, x_15, x_16, x_308);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = l_List_isEmpty___redArg(x_307);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_313);
x_315 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_307);
lean_inc(x_8);
x_316 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_8, x_6, x_307, x_307, x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_312);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
x_319 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_307, x_7);
lean_dec(x_307);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_317);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_st_ref_take(x_14, x_317);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_321, 3);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_323, 3);
lean_inc(x_328);
x_329 = lean_ctor_get(x_323, 4);
lean_inc(x_329);
lean_dec(x_323);
x_330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_330, 2, x_327);
lean_ctor_set(x_330, 3, x_328);
lean_ctor_set(x_330, 4, x_329);
x_331 = lean_st_ref_set(x_14, x_330, x_324);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_321, 2);
lean_inc(x_334);
lean_dec(x_321);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_337 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_8, x_335, x_336, x_13, x_14, x_15, x_16, x_332);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_334, 2);
lean_inc(x_341);
lean_dec(x_334);
if (lean_is_scalar(x_333)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_333;
 lean_ctor_set_tag(x_342, 1);
}
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_342, x_10, x_13, x_14, x_15, x_16, x_339);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_344 = lean_ctor_get(x_337, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_337, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_346 = x_337;
} else {
 lean_dec_ref(x_337);
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
}
}
else
{
lean_dec(x_307);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_316;
}
}
else
{
lean_object* x_348; 
lean_dec(x_307);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_13);
x_348 = l_Lean_FVarId_getUserName(x_8, x_13, x_14, x_15, x_16, x_312);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the hypothesis ", 59, 59);
x_352 = l_Lean_stringToMessageData(x_351);
lean_dec(x_351);
x_353 = l_Lean_MessageData_ofName(x_349);
if (lean_is_scalar(x_313)) {
 x_354 = lean_alloc_ctor(7, 2, 0);
} else {
 x_354 = x_313;
 lean_ctor_set_tag(x_354, 7);
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_mk_string_unchecked("", 0, 0);
x_356 = l_Lean_stringToMessageData(x_355);
lean_dec(x_355);
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_356);
x_358 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_357, x_13, x_14, x_15, x_16, x_350);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_313);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_359 = lean_ctor_get(x_348, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
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
lean_dec(x_2);
x_363 = lean_ctor_get(x_306, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_306, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_365 = x_306;
} else {
 lean_dec_ref(x_306);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_294);
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
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_299, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_299, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_369 = x_299;
} else {
 lean_dec_ref(x_299);
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
lean_dec(x_2);
lean_dec(x_1);
x_371 = lean_ctor_get(x_290, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_290, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_373 = x_290;
} else {
 lean_dec_ref(x_290);
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
lean_object* x_375; lean_object* x_376; 
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
lean_dec(x_2);
lean_dec(x_1);
x_375 = lean_box(0);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_287);
return x_376;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l_Lean_MVarId_getType(x_1, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_22, x_17, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_28 = l_Lean_Meta_Rewrites_localHypotheses(x_27, x_16, x_17, x_18, x_19, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(2);
x_32 = lean_unsigned_to_nat(20u);
x_33 = lean_unsigned_to_nat(10u);
x_34 = lean_unbox(x_31);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_35 = l_Lean_Meta_Rewrites_findRewrites(x_29, x_2, x_1, x_25, x_3, x_34, x_4, x_32, x_33, x_16, x_17, x_18, x_19, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_mk_string_unchecked("rewrites", 8, 8);
x_39 = l_Lean_Name_mkStr1(x_38);
lean_inc(x_18);
x_40 = l_Lean_reportOutOfHeartbeats(x_39, x_5, x_6, x_18, x_19, x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_List_isEmpty___redArg(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_Elab_Tactic_saveState___redArg(x_13, x_15, x_17, x_18, x_19, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Init_GetElem_0__List_get_x3fInternal(lean_box(0), x_36, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_47 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_44, x_8, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_44);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_take(x_17, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_48, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 4);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_55);
lean_ctor_set(x_57, 4, x_56);
x_58 = lean_st_ref_set(x_17, x_57, x_51);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Elab_Tactic_saveState___redArg(x_13, x_15, x_17, x_18, x_19, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_ctor_get(x_48, 2);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_67 = l_Lean_MVarId_replaceTargetEq(x_1, x_65, x_66, x_16, x_17, x_18, x_19, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_64, 2);
lean_inc(x_70);
lean_dec(x_64);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_70);
lean_ctor_set(x_60, 0, x_68);
x_71 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_60, x_13, x_16, x_17, x_18, x_19, x_69);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_71, 1);
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
x_75 = lean_st_ref_get(x_19, x_73);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_18, 5);
lean_inc(x_79);
x_80 = l_Lean_SourceInfo_fromRef(x_79, x_42);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_82 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_81);
x_83 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_80);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_83);
lean_ctor_set(x_75, 0, x_80);
x_84 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_85 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_84);
x_86 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_87 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_86);
x_88 = lean_mk_string_unchecked("null", 4, 4);
x_89 = l_Lean_Name_mkStr1(x_88);
x_90 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_91 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_90);
x_92 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_80);
lean_ctor_set_tag(x_71, 2);
lean_ctor_set(x_71, 1, x_92);
lean_ctor_set(x_71, 0, x_80);
lean_inc(x_80);
x_93 = l_Lean_Syntax_node1(x_80, x_91, x_71);
lean_inc(x_80);
x_94 = l_Lean_Syntax_node1(x_80, x_89, x_93);
lean_inc(x_80);
x_95 = l_Lean_Syntax_node1(x_80, x_87, x_94);
lean_inc(x_80);
x_96 = l_Lean_Syntax_node1(x_80, x_85, x_95);
x_97 = l_Lean_Syntax_node2(x_80, x_82, x_75, x_96);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_98 = l_Lean_Elab_Tactic_evalTactic(x_97, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_77);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_62, x_8, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_99);
return x_100;
}
else
{
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_98;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_75, 1);
lean_inc(x_101);
lean_dec(x_75);
x_102 = lean_ctor_get(x_18, 5);
lean_inc(x_102);
x_103 = l_Lean_SourceInfo_fromRef(x_102, x_42);
lean_dec(x_102);
x_104 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_105 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_104);
x_106 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_103);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_109 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_108);
x_110 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_111 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_110);
x_112 = lean_mk_string_unchecked("null", 4, 4);
x_113 = l_Lean_Name_mkStr1(x_112);
x_114 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_115 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_114);
x_116 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_103);
lean_ctor_set_tag(x_71, 2);
lean_ctor_set(x_71, 1, x_116);
lean_ctor_set(x_71, 0, x_103);
lean_inc(x_103);
x_117 = l_Lean_Syntax_node1(x_103, x_115, x_71);
lean_inc(x_103);
x_118 = l_Lean_Syntax_node1(x_103, x_113, x_117);
lean_inc(x_103);
x_119 = l_Lean_Syntax_node1(x_103, x_111, x_118);
lean_inc(x_103);
x_120 = l_Lean_Syntax_node1(x_103, x_109, x_119);
x_121 = l_Lean_Syntax_node2(x_103, x_105, x_107, x_120);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_122 = l_Lean_Elab_Tactic_evalTactic(x_121, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_101);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_62, x_8, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_123);
return x_124;
}
else
{
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_122;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_125 = lean_ctor_get(x_71, 1);
lean_inc(x_125);
lean_dec(x_71);
x_126 = lean_st_ref_get(x_19, x_125);
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
x_129 = lean_ctor_get(x_18, 5);
lean_inc(x_129);
x_130 = l_Lean_SourceInfo_fromRef(x_129, x_42);
lean_dec(x_129);
x_131 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_132 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_131);
x_133 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_130);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(2, 2, 0);
} else {
 x_134 = x_128;
 lean_ctor_set_tag(x_134, 2);
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_136 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_135);
x_137 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_138 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_137);
x_139 = lean_mk_string_unchecked("null", 4, 4);
x_140 = l_Lean_Name_mkStr1(x_139);
x_141 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_142 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_141);
x_143 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_130);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_130);
x_145 = l_Lean_Syntax_node1(x_130, x_142, x_144);
lean_inc(x_130);
x_146 = l_Lean_Syntax_node1(x_130, x_140, x_145);
lean_inc(x_130);
x_147 = l_Lean_Syntax_node1(x_130, x_138, x_146);
lean_inc(x_130);
x_148 = l_Lean_Syntax_node1(x_130, x_136, x_147);
x_149 = l_Lean_Syntax_node2(x_130, x_132, x_134, x_148);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_150 = l_Lean_Elab_Tactic_evalTactic(x_149, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_127);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_62, x_8, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_151);
return x_152;
}
else
{
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_150;
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_71;
}
}
else
{
uint8_t x_153; 
lean_dec(x_64);
lean_free_object(x_60);
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_153 = !lean_is_exclusive(x_67);
if (x_153 == 0)
{
return x_67;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_67, 0);
x_155 = lean_ctor_get(x_67, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_67);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_60, 0);
x_158 = lean_ctor_get(x_60, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_60);
x_159 = lean_ctor_get(x_48, 2);
lean_inc(x_159);
lean_dec(x_48);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_162 = l_Lean_MVarId_replaceTargetEq(x_1, x_160, x_161, x_16, x_17, x_18, x_19, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_159, 2);
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_166, x_13, x_16, x_17, x_18, x_19, x_164);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_st_ref_get(x_19, x_168);
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
x_173 = lean_ctor_get(x_18, 5);
lean_inc(x_173);
x_174 = l_Lean_SourceInfo_fromRef(x_173, x_42);
lean_dec(x_173);
x_175 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_176 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_175);
x_177 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_174);
if (lean_is_scalar(x_172)) {
 x_178 = lean_alloc_ctor(2, 2, 0);
} else {
 x_178 = x_172;
 lean_ctor_set_tag(x_178, 2);
}
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_180 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_179);
x_181 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_182 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_181);
x_183 = lean_mk_string_unchecked("null", 4, 4);
x_184 = l_Lean_Name_mkStr1(x_183);
x_185 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_186 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_185);
x_187 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_174);
if (lean_is_scalar(x_169)) {
 x_188 = lean_alloc_ctor(2, 2, 0);
} else {
 x_188 = x_169;
 lean_ctor_set_tag(x_188, 2);
}
lean_ctor_set(x_188, 0, x_174);
lean_ctor_set(x_188, 1, x_187);
lean_inc(x_174);
x_189 = l_Lean_Syntax_node1(x_174, x_186, x_188);
lean_inc(x_174);
x_190 = l_Lean_Syntax_node1(x_174, x_184, x_189);
lean_inc(x_174);
x_191 = l_Lean_Syntax_node1(x_174, x_182, x_190);
lean_inc(x_174);
x_192 = l_Lean_Syntax_node1(x_174, x_180, x_191);
x_193 = l_Lean_Syntax_node2(x_174, x_176, x_178, x_192);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_194 = l_Lean_Elab_Tactic_evalTactic(x_193, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_171);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_157, x_8, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_195);
return x_196;
}
else
{
lean_dec(x_157);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_194;
}
}
else
{
lean_dec(x_157);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_167;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_197 = lean_ctor_get(x_162, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_162, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_199 = x_162;
} else {
 lean_dec_ref(x_162);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_36);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_201 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the goal", 52, 52);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_202, x_16, x_17, x_18, x_19, x_41);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_203;
}
}
else
{
uint8_t x_204; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_35);
if (x_204 == 0)
{
return x_35;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_35, 0);
x_206 = lean_ctor_get(x_35, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_35);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_28);
if (x_208 == 0)
{
return x_28;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_28, 0);
x_210 = lean_ctor_get(x_28, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_28);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_21);
if (x_212 == 0)
{
return x_21;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_21, 0);
x_214 = lean_ctor_get(x_21, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_21);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_mk_string_unchecked("Lean", 4, 4);
x_29 = lean_mk_string_unchecked("Parser", 6, 6);
x_30 = lean_mk_string_unchecked("Tactic", 6, 6);
x_31 = lean_mk_string_unchecked("rewrites\?", 9, 9);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_32 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_31);
lean_inc(x_1);
x_33 = l_Lean_Syntax_isOfKind(x_1, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_170; uint8_t x_171; 
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__0___boxed), 10, 0);
x_36 = lean_unsigned_to_nat(0u);
x_135 = lean_unsigned_to_nat(1u);
x_170 = l_Lean_Syntax_getArg(x_1, x_135);
x_171 = l_Lean_Syntax_isNone(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
lean_inc(x_170);
x_172 = l_Lean_Syntax_matchesNull(x_170, x_135);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Lean_Syntax_getArg(x_170, x_36);
lean_dec(x_170);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_136 = x_175;
x_137 = x_2;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
goto block_169;
}
}
else
{
lean_object* x_176; 
lean_dec(x_170);
x_176 = lean_box(0);
x_136 = x_176;
x_137 = x_2;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
goto block_169;
}
block_60:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_1);
lean_inc(x_37);
lean_inc(x_39);
lean_inc(x_52);
lean_inc(x_40);
lean_inc(x_38);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 17, 7);
lean_closure_set(x_53, 0, x_38);
lean_closure_set(x_53, 1, x_40);
lean_closure_set(x_53, 2, x_52);
lean_closure_set(x_53, 3, x_39);
lean_closure_set(x_53, 4, x_37);
lean_closure_set(x_53, 5, x_1);
lean_closure_set(x_53, 6, x_36);
x_54 = lean_box(x_33);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 20, 11);
lean_closure_set(x_55, 0, x_40);
lean_closure_set(x_55, 1, x_38);
lean_closure_set(x_55, 2, x_52);
lean_closure_set(x_55, 3, x_54);
lean_closure_set(x_55, 4, x_39);
lean_closure_set(x_55, 5, x_37);
lean_closure_set(x_55, 6, x_36);
lean_closure_set(x_55, 7, x_1);
lean_closure_set(x_55, 8, x_28);
lean_closure_set(x_55, 9, x_29);
lean_closure_set(x_55, 10, x_30);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_11 = x_42;
x_12 = x_45;
x_13 = x_44;
x_14 = x_43;
x_15 = x_47;
x_16 = x_46;
x_17 = x_48;
x_18 = x_50;
x_19 = x_53;
x_20 = x_55;
x_21 = x_41;
x_22 = x_51;
x_23 = x_56;
goto block_27;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
x_11 = x_42;
x_12 = x_45;
x_13 = x_44;
x_14 = x_43;
x_15 = x_47;
x_16 = x_46;
x_17 = x_48;
x_18 = x_50;
x_19 = x_53;
x_20 = x_55;
x_21 = x_41;
x_22 = x_51;
x_23 = x_49;
goto block_27;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_11 = x_42;
x_12 = x_45;
x_13 = x_44;
x_14 = x_43;
x_15 = x_47;
x_16 = x_46;
x_17 = x_48;
x_18 = x_50;
x_19 = x_53;
x_20 = x_55;
x_21 = x_41;
x_22 = x_51;
x_23 = x_59;
goto block_27;
}
}
}
block_95:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_mk_string_unchecked("findRewrites", 12, 12);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_unsigned_to_nat(90u);
lean_inc(x_73);
x_78 = l_Lean_reportOutOfHeartbeats(x_76, x_63, x_77, x_73, x_69, x_61);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Elab_Tactic_getMainGoal(x_66, x_68, x_67, x_72, x_64, x_65, x_73, x_69, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_array_size(x_74);
x_84 = lean_usize_of_nat(x_36);
x_85 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_getBracketedBinderIds_spec__0(x_83, x_84, x_74);
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_lt(x_36, x_86);
if (x_87 == 0)
{
lean_dec(x_86);
lean_dec(x_85);
x_37 = x_77;
x_38 = x_62;
x_39 = x_63;
x_40 = x_81;
x_41 = x_82;
x_42 = x_64;
x_43 = x_35;
x_44 = x_66;
x_45 = x_65;
x_46 = x_68;
x_47 = x_67;
x_48 = x_69;
x_49 = x_70;
x_50 = x_72;
x_51 = x_73;
x_52 = x_71;
goto block_60;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_86, x_86);
if (x_88 == 0)
{
lean_dec(x_86);
lean_dec(x_85);
x_37 = x_77;
x_38 = x_62;
x_39 = x_63;
x_40 = x_81;
x_41 = x_82;
x_42 = x_64;
x_43 = x_35;
x_44 = x_66;
x_45 = x_65;
x_46 = x_68;
x_47 = x_67;
x_48 = x_69;
x_49 = x_70;
x_50 = x_72;
x_51 = x_73;
x_52 = x_71;
goto block_60;
}
else
{
size_t x_89; lean_object* x_90; 
x_89 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_90 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3(x_85, x_84, x_89, x_71);
lean_dec(x_85);
x_37 = x_77;
x_38 = x_62;
x_39 = x_63;
x_40 = x_81;
x_41 = x_82;
x_42 = x_64;
x_43 = x_35;
x_44 = x_66;
x_45 = x_65;
x_46 = x_68;
x_47 = x_67;
x_48 = x_69;
x_49 = x_70;
x_50 = x_72;
x_51 = x_73;
x_52 = x_90;
goto block_60;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_80);
if (x_91 == 0)
{
return x_80;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
block_118:
{
lean_object* x_107; 
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
x_107 = l_Lean_Meta_Rewrites_createModuleTreeRef(x_102, x_103, x_104, x_105, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Syntax_getArg(x_1, x_36);
x_111 = lean_box(0);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_112; 
x_112 = lean_mk_empty_array_with_capacity(x_36);
x_61 = x_109;
x_62 = x_108;
x_63 = x_110;
x_64 = x_102;
x_65 = x_103;
x_66 = x_98;
x_67 = x_100;
x_68 = x_99;
x_69 = x_105;
x_70 = x_96;
x_71 = x_111;
x_72 = x_101;
x_73 = x_104;
x_74 = x_112;
goto block_95;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
x_61 = x_109;
x_62 = x_108;
x_63 = x_110;
x_64 = x_102;
x_65 = x_103;
x_66 = x_98;
x_67 = x_100;
x_68 = x_99;
x_69 = x_105;
x_70 = x_96;
x_71 = x_111;
x_72 = x_101;
x_73 = x_104;
x_74 = x_113;
goto block_95;
}
}
else
{
uint8_t x_114; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_134:
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = lean_array_size(x_129);
x_131 = lean_usize_of_nat(x_36);
x_132 = l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4(x_130, x_131, x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_133 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_121);
return x_133;
}
else
{
x_96 = x_123;
x_97 = x_132;
x_98 = x_122;
x_99 = x_125;
x_100 = x_120;
x_101 = x_124;
x_102 = x_119;
x_103 = x_128;
x_104 = x_126;
x_105 = x_127;
x_106 = x_121;
goto block_118;
}
}
block_169:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_unsigned_to_nat(2u);
x_147 = l_Lean_Syntax_getArg(x_1, x_146);
x_148 = l_Lean_Syntax_isNone(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_inc(x_147);
x_149 = l_Lean_Syntax_matchesNull(x_147, x_135);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_150 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_145);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = l_Lean_Syntax_getArg(x_147, x_36);
lean_dec(x_147);
x_152 = lean_mk_string_unchecked("rewrites_forbidden", 18, 18);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_153 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_152);
lean_inc(x_151);
x_154 = l_Lean_Syntax_isOfKind(x_151, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_151);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_155 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_145);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = l_Lean_Syntax_getArg(x_151, x_135);
lean_dec(x_151);
x_157 = l_Lean_Syntax_getArgs(x_156);
lean_dec(x_156);
x_158 = l_Array_empty(lean_box(0));
x_159 = lean_array_get_size(x_157);
x_160 = lean_nat_dec_lt(x_36, x_159);
if (x_160 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_119 = x_141;
x_120 = x_139;
x_121 = x_145;
x_122 = x_137;
x_123 = x_136;
x_124 = x_140;
x_125 = x_138;
x_126 = x_143;
x_127 = x_144;
x_128 = x_142;
x_129 = x_158;
goto block_134;
}
else
{
uint8_t x_161; 
x_161 = lean_nat_dec_le(x_159, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_119 = x_141;
x_120 = x_139;
x_121 = x_145;
x_122 = x_137;
x_123 = x_136;
x_124 = x_140;
x_125 = x_138;
x_126 = x_143;
x_127 = x_144;
x_128 = x_142;
x_129 = x_158;
goto block_134;
}
else
{
lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_box(x_154);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
x_164 = lean_usize_of_nat(x_36);
x_165 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_166 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5(x_1, x_157, x_164, x_165, x_163);
lean_dec(x_157);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_119 = x_141;
x_120 = x_139;
x_121 = x_145;
x_122 = x_137;
x_123 = x_136;
x_124 = x_140;
x_125 = x_138;
x_126 = x_143;
x_127 = x_144;
x_128 = x_142;
x_129 = x_167;
goto block_134;
}
}
}
}
}
else
{
lean_object* x_168; 
lean_dec(x_147);
x_168 = lean_box(0);
x_96 = x_136;
x_97 = x_168;
x_98 = x_137;
x_99 = x_138;
x_100 = x_139;
x_101 = x_140;
x_102 = x_141;
x_103 = x_142;
x_104 = x_143;
x_105 = x_144;
x_106 = x_145;
goto block_118;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_mkOptionalNode(x_23);
x_25 = l_Lean_Elab_Tactic_expandOptLocation(x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_Tactic_withLocation(x_25, x_19, x_20, x_14, x_13, x_16, x_15, x_18, x_11, x_12, x_22, x_17, x_21);
lean_dec(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___at___Lean_Elab_Rewrites_evalExact_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___Lean_Elab_Rewrites_evalExact_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Rewrites_evalExact_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Rewrites_evalExact_spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Rewrites_evalExact___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object** _args) {
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
x_18 = l_Lean_Elab_Rewrites_evalExact___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object** _args) {
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
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = l_Lean_Elab_Rewrites_evalExact___lam__2(x_1, x_2, x_3, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Rewrites_evalExact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("rewrites\?", 9, 9);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Rewrites", 8, 8);
x_10 = lean_mk_string_unchecked("evalExact", 9, 9);
x_11 = l_Lean_Name_mkStr4(x_3, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Rewrites", 8, 8);
x_5 = lean_mk_string_unchecked("evalExact", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(29u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(67u);
x_11 = lean_unsigned_to_nat(70u);
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
x_16 = lean_unsigned_to_nat(13u);
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
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrites(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Rewrites_evalExact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
