// Lean compiler output
// Module: Lean.Elab.Tactic.Change
// Imports: Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Location
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_docString__1(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_box(1);
x_15 = lean_box(0);
x_16 = lean_unbox(x_14);
x_17 = lean_unbox(x_14);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_13, x_16, x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_19);
x_21 = l_Lean_Meta_isExprDefEq(x_19, x_1, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(2);
x_26 = lean_unbox(x_25);
x_27 = lean_unbox(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_19);
x_30 = l_Lean_Meta_isExprDefEq(x_19, x_1, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_21, 0);
lean_dec(x_44);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
lean_dec(x_1);
return x_18;
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
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange___lam__0), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_Tactic_runTermElab___redArg(x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, 0);
x_21 = lean_ctor_get_uint8(x_19, 1);
x_22 = lean_ctor_get_uint8(x_19, 2);
x_23 = lean_ctor_get_uint8(x_19, 3);
x_24 = lean_ctor_get_uint8(x_19, 4);
x_25 = lean_ctor_get_uint8(x_19, 5);
x_26 = lean_ctor_get_uint8(x_19, 6);
x_27 = lean_box(1);
x_28 = lean_ctor_get_uint8(x_19, 8);
x_29 = lean_ctor_get_uint8(x_19, 9);
x_30 = lean_ctor_get_uint8(x_19, 10);
x_31 = lean_ctor_get_uint8(x_19, 11);
x_32 = lean_ctor_get_uint8(x_19, 12);
x_33 = lean_ctor_get_uint8(x_19, 13);
x_34 = lean_ctor_get_uint8(x_19, 14);
x_35 = lean_ctor_get_uint8(x_19, 15);
x_36 = lean_ctor_get_uint8(x_19, 16);
x_37 = lean_ctor_get_uint8(x_19, 17);
lean_dec(x_19);
x_38 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_38, 0, x_20);
lean_ctor_set_uint8(x_38, 1, x_21);
lean_ctor_set_uint8(x_38, 2, x_22);
lean_ctor_set_uint8(x_38, 3, x_23);
lean_ctor_set_uint8(x_38, 4, x_24);
lean_ctor_set_uint8(x_38, 5, x_25);
lean_ctor_set_uint8(x_38, 6, x_26);
x_39 = lean_unbox(x_27);
lean_ctor_set_uint8(x_38, 7, x_39);
lean_ctor_set_uint8(x_38, 8, x_28);
lean_ctor_set_uint8(x_38, 9, x_29);
lean_ctor_set_uint8(x_38, 10, x_30);
lean_ctor_set_uint8(x_38, 11, x_31);
lean_ctor_set_uint8(x_38, 12, x_32);
lean_ctor_set_uint8(x_38, 13, x_33);
lean_ctor_set_uint8(x_38, 14, x_34);
lean_ctor_set_uint8(x_38, 15, x_35);
lean_ctor_set_uint8(x_38, 16, x_36);
lean_ctor_set_uint8(x_38, 17, x_37);
x_40 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_38);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 6);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_dec(x_7);
x_50 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set_uint64(x_50, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 10, x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_17);
x_51 = l_Lean_Meta_isExprDefEq(x_17, x_1, x_50, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_50);
x_55 = l_Lean_Meta_addPPExplicitToExposeDiff(x_17, x_1, x_50, x_8, x_9, x_10, x_54);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_mk_string_unchecked("'change' tactic failed, pattern", 31, 31);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = l_Lean_indentExpr(x_59);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_63);
lean_ctor_set(x_56, 0, x_62);
x_64 = lean_mk_string_unchecked("\nis not definitionally equal to target", 38, 38);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_65);
lean_ctor_set(x_15, 0, x_56);
x_66 = l_Lean_indentExpr(x_60);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_15);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_70, x_50, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_50);
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_78 = lean_mk_string_unchecked("'change' tactic failed, pattern", 31, 31);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = l_Lean_indentExpr(x_76);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("\nis not definitionally equal to target", 38, 38);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_83);
lean_ctor_set(x_15, 0, x_81);
x_84 = l_Lean_indentExpr(x_77);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("", 0, 0);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_88, x_50, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_50);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
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
uint8_t x_94; 
lean_dec(x_50);
lean_free_object(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_50);
lean_free_object(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_98 = lean_ctor_get(x_51, 1);
lean_inc(x_98);
lean_dec(x_51);
x_99 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_17, x_8, x_98);
lean_dec(x_8);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_50);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_51);
if (x_104 == 0)
{
return x_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_51, 0);
x_106 = lean_ctor_get(x_51, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_51);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; uint64_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_108 = lean_ctor_get(x_15, 0);
x_109 = lean_ctor_get(x_15, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_15);
x_110 = lean_ctor_get(x_7, 0);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_110, 0);
x_112 = lean_ctor_get_uint8(x_110, 1);
x_113 = lean_ctor_get_uint8(x_110, 2);
x_114 = lean_ctor_get_uint8(x_110, 3);
x_115 = lean_ctor_get_uint8(x_110, 4);
x_116 = lean_ctor_get_uint8(x_110, 5);
x_117 = lean_ctor_get_uint8(x_110, 6);
x_118 = lean_box(1);
x_119 = lean_ctor_get_uint8(x_110, 8);
x_120 = lean_ctor_get_uint8(x_110, 9);
x_121 = lean_ctor_get_uint8(x_110, 10);
x_122 = lean_ctor_get_uint8(x_110, 11);
x_123 = lean_ctor_get_uint8(x_110, 12);
x_124 = lean_ctor_get_uint8(x_110, 13);
x_125 = lean_ctor_get_uint8(x_110, 14);
x_126 = lean_ctor_get_uint8(x_110, 15);
x_127 = lean_ctor_get_uint8(x_110, 16);
x_128 = lean_ctor_get_uint8(x_110, 17);
lean_dec(x_110);
x_129 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_129, 0, x_111);
lean_ctor_set_uint8(x_129, 1, x_112);
lean_ctor_set_uint8(x_129, 2, x_113);
lean_ctor_set_uint8(x_129, 3, x_114);
lean_ctor_set_uint8(x_129, 4, x_115);
lean_ctor_set_uint8(x_129, 5, x_116);
lean_ctor_set_uint8(x_129, 6, x_117);
x_130 = lean_unbox(x_118);
lean_ctor_set_uint8(x_129, 7, x_130);
lean_ctor_set_uint8(x_129, 8, x_119);
lean_ctor_set_uint8(x_129, 9, x_120);
lean_ctor_set_uint8(x_129, 10, x_121);
lean_ctor_set_uint8(x_129, 11, x_122);
lean_ctor_set_uint8(x_129, 12, x_123);
lean_ctor_set_uint8(x_129, 13, x_124);
lean_ctor_set_uint8(x_129, 14, x_125);
lean_ctor_set_uint8(x_129, 15, x_126);
lean_ctor_set_uint8(x_129, 16, x_127);
lean_ctor_set_uint8(x_129, 17, x_128);
x_131 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_129);
x_132 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_133 = lean_ctor_get(x_7, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_7, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_7, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_7, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_7, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_7, 6);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_140 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_dec(x_7);
x_141 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_141, 0, x_129);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_134);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set(x_141, 4, x_136);
lean_ctor_set(x_141, 5, x_137);
lean_ctor_set(x_141, 6, x_138);
lean_ctor_set_uint64(x_141, sizeof(void*)*7, x_131);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 8, x_132);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 9, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 10, x_140);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_108);
x_142 = l_Lean_Meta_isExprDefEq(x_108, x_1, x_141, x_8, x_9, x_10, x_109);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_141);
x_146 = l_Lean_Meta_addPPExplicitToExposeDiff(x_108, x_1, x_141, x_8, x_9, x_10, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
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
x_152 = lean_mk_string_unchecked("'change' tactic failed, pattern", 31, 31);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = l_Lean_indentExpr(x_149);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_151;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_mk_string_unchecked("\nis not definitionally equal to target", 38, 38);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_indentExpr(x_150);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_163, x_141, x_8, x_9, x_10, x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_141);
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
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_169 = lean_ctor_get(x_146, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_146, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_171 = x_146;
} else {
 lean_dec_ref(x_146);
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
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_173 = lean_ctor_get(x_142, 1);
lean_inc(x_173);
lean_dec(x_142);
x_174 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_108, x_8, x_173);
lean_dec(x_8);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_141);
lean_dec(x_108);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_179 = lean_ctor_get(x_142, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_142, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_181 = x_142;
} else {
 lean_dec_ref(x_142);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_mk_string_unchecked("'change' tactic failed", 22, 22);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_MVarId_replaceTargetDefEq(x_13, x_1, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_19 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_18, x_4, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
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
else
{
return x_19;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
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
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainTarget(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_getMainTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange), 11, 2);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_1);
x_19 = l_Lean_Name_mkStr1(x_2);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_18, x_16, x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1___boxed), 11, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_withMainContext___redArg(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_7);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_13);
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
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_MVarId_changeLocalDecl(x_15, x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_4);
x_21 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_20, x_6, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
return x_21;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_FVarId_getType___redArg(x_4, x_9, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabChange), 11, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_1);
x_21 = l_Lean_Name_mkStr1(x_2);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_20, x_18, x_21, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(x_3);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3___boxed), 13, 4);
lean_closure_set(x_30, 0, x_4);
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_28);
x_31 = l_Lean_Elab_Tactic_withMainContext___redArg(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_9);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
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
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
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
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("change", 6, 6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0___boxed), 10, 0);
x_35 = lean_unsigned_to_nat(1u);
x_55 = lean_unsigned_to_nat(2u);
x_56 = l_Lean_Syntax_getArg(x_1, x_55);
x_57 = l_Lean_Syntax_isNone(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_inc(x_56);
x_58 = l_Lean_Syntax_matchesNull(x_56, x_35);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Syntax_getArg(x_56, x_60);
lean_dec(x_56);
x_62 = lean_mk_string_unchecked("location", 8, 8);
x_63 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_62);
lean_inc(x_61);
x_64 = l_Lean_Syntax_isOfKind(x_61, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_36 = x_66;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_7;
x_43 = x_8;
x_44 = x_9;
x_45 = x_10;
goto block_54;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_67 = lean_box(0);
x_36 = x_67;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_7;
x_43 = x_8;
x_44 = x_9;
x_45 = x_10;
goto block_54;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_mkOptionalNode(x_30);
x_32 = l_Lean_Elab_Tactic_expandOptLocation(x_31);
lean_dec(x_31);
x_33 = l_Lean_Elab_Tactic_withLocation(x_32, x_25, x_28, x_18, x_23, x_27, x_20, x_29, x_21, x_22, x_26, x_19, x_24);
lean_dec(x_32);
return x_33;
}
block_54:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
lean_inc(x_14);
lean_inc(x_46);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__2), 11, 2);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_14);
x_48 = lean_box(x_16);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4___boxed), 13, 3);
lean_closure_set(x_49, 0, x_46);
lean_closure_set(x_49, 1, x_14);
lean_closure_set(x_49, 2, x_48);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_19 = x_44;
x_20 = x_39;
x_21 = x_41;
x_22 = x_42;
x_23 = x_37;
x_24 = x_45;
x_25 = x_49;
x_26 = x_43;
x_27 = x_38;
x_28 = x_47;
x_29 = x_40;
x_30 = x_50;
goto block_34;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_36);
if (x_51 == 0)
{
x_19 = x_44;
x_20 = x_39;
x_21 = x_41;
x_22 = x_42;
x_23 = x_37;
x_24 = x_45;
x_25 = x_49;
x_26 = x_43;
x_27 = x_38;
x_28 = x_47;
x_29 = x_40;
x_30 = x_36;
goto block_34;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_19 = x_44;
x_20 = x_39;
x_21 = x_41;
x_22 = x_42;
x_23 = x_37;
x_24 = x_45;
x_25 = x_49;
x_26 = x_43;
x_27 = x_38;
x_28 = x_47;
x_29 = x_40;
x_30 = x_53;
goto block_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1___lam__4(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("change", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("_aux_Lean_Elab_Tactic_Change___elabRules_Lean_Parser_Tactic_change_1", 68, 68);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("_aux_Lean_Elab_Tactic_Change___elabRules_Lean_Parser_Tactic_change_1", 68, 68);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`change` can be used to replace the main goal or its hypotheses with\ndifferent, yet definitionally equal, goal or hypotheses.\n\nFor example, if `n : Nat` and the current goal is `⊢ n + 2 = 2`, then\n```lean\nchange _ + 1 = _\n```\nchanges the goal to `⊢ n + 1 + 1 = 2`.\n\nThe tactic also applies to hypotheses. If `h : n + 2 = 2` and `h' : n + 3 = 4`\nare hypotheses, then\n```lean\nchange _ + 1 = _ at h h'\n```\nchanges their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.\n\nChange is like `refine` in that every placeholder needs to be solved for by unification,\nbut using named placeholders or `\?_` results in `change` to creating new goals.\n\nThe tactic `show e` is interchangeable with `change e`, where the pattern `e` is applied to\nthe main goal. ", 757, 753);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("_aux_Lean_Elab_Tactic_Change___elabRules_Lean_Parser_Tactic_change_1", 68, 68);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(16u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(50u);
x_11 = lean_unsigned_to_nat(60u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_addBuiltinDeclarationRanges(x_6, x_14, x_1);
return x_15;
}
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic___aux__Lean__Elab__Tactic__Change______elabRules__Lean__Parser__Tactic__change__1_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
