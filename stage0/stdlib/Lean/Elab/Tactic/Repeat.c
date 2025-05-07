// Lean compiler output
// Module: Lean.Elab.Tactic.Repeat
// Imports: Lean.Meta.Tactic.Repeat Lean.Elab.Tactic.Basic
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
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__1(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___Lean_Elab_Tactic_pruneSolvedGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_40; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
x_40 = l_Lean_Exception_isInterrupt(x_25);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isRuntime(x_25);
x_28 = x_41;
goto block_39;
}
else
{
x_28 = x_40;
goto block_39;
}
block_39:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Lean_Elab_Tactic_SavedState_restore(x_15, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_27)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_27;
}
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_16 = lean_box(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = l_Lean_MVarId_isAssigned___at___Lean_Elab_Tactic_pruneSolvedGoals_spec__0(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_2, x_31);
if (x_32 == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_4);
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
x_33 = lean_array_push(x_6, x_23);
x_34 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_33, x_24);
x_35 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__0(x_34, x_5);
x_36 = lean_box(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_25, 0, x_37);
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_25);
lean_inc(x_1);
lean_inc(x_23);
x_38 = lean_apply_1(x_1, x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_2, x_42);
lean_dec(x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; 
lean_free_object(x_4);
x_44 = lean_array_push(x_6, x_23);
x_2 = x_43;
x_4 = x_24;
x_6 = x_44;
x_15 = x_41;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_23);
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(1);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_24);
x_48 = lean_unbox(x_47);
{
lean_object* _tmp_1 = x_43;
uint8_t _tmp_2 = x_48;
lean_object* _tmp_3 = x_46;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_14 = x_41;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_15 = _tmp_14;
}
goto _start;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_23);
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
lean_dec(x_1);
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
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_2, x_55);
if (x_56 == 1)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_4);
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
x_57 = lean_array_push(x_6, x_23);
x_58 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_57, x_24);
x_59 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__0(x_58, x_5);
x_60 = lean_box(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_inc(x_1);
lean_inc(x_23);
x_63 = lean_apply_1(x_1, x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_64 = l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(x_63, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_2, x_67);
lean_dec(x_2);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_69; 
lean_free_object(x_4);
x_69 = lean_array_push(x_6, x_23);
x_2 = x_68;
x_4 = x_24;
x_6 = x_69;
x_15 = x_66;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_23);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_box(1);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_24);
x_73 = lean_unbox(x_72);
{
lean_object* _tmp_1 = x_68;
uint8_t _tmp_2 = x_73;
lean_object* _tmp_3 = x_71;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_14 = x_66;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_15 = _tmp_14;
}
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_23);
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
lean_dec(x_1);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_77 = x_64;
} else {
 lean_dec_ref(x_64);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
lean_free_object(x_4);
lean_dec(x_23);
x_79 = lean_ctor_get(x_25, 1);
lean_inc(x_79);
lean_dec(x_25);
x_4 = x_24;
x_15 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_4, 0);
x_82 = lean_ctor_get(x_4, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_4);
x_83 = l_Lean_MVarId_isAssigned___at___Lean_Elab_Tactic_pruneSolvedGoals_spec__0(x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_2, x_88);
if (x_89 == 1)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
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
x_90 = lean_array_push(x_6, x_81);
x_91 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_90, x_82);
x_92 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__0(x_91, x_5);
x_93 = lean_box(x_3);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
if (lean_is_scalar(x_87)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_87;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_86);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_87);
lean_inc(x_1);
lean_inc(x_81);
x_96 = lean_apply_1(x_1, x_81);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_97 = l_Lean_observing_x3f___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0_spec__1___redArg(x_96, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_86);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_2, x_100);
lean_dec(x_2);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_102; 
x_102 = lean_array_push(x_6, x_81);
x_2 = x_101;
x_4 = x_82;
x_6 = x_102;
x_15 = x_99;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_81);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_5);
x_107 = lean_unbox(x_105);
x_2 = x_101;
x_3 = x_107;
x_4 = x_104;
x_5 = x_106;
x_15 = x_99;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_82);
lean_dec(x_81);
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
lean_dec(x_1);
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
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
lean_object* x_113; 
lean_dec(x_81);
x_113 = lean_ctor_get(x_83, 1);
lean_inc(x_113);
lean_dec(x_83);
x_4 = x_82;
x_15 = x_113;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_2, x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_array_uget(x_1, x_2);
x_26 = l_Lean_MVarId_isAssigned___at___Lean_Elab_Tactic_pruneSolvedGoals_spec__0(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_23 = x_29;
goto block_25;
}
else
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_14 = x_4;
x_15 = x_30;
goto block_20;
}
block_25:
{
lean_object* x_24; 
x_24 = lean_array_push(x_4, x_22);
x_14 = x_24;
x_15 = x_23;
goto block_20;
}
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_unbox(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_18 = l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0(x_1, x_3, x_17, x_2, x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; uint8_t x_32; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_31 = lean_array_get_size(x_23);
x_32 = lean_nat_dec_lt(x_15, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = x_16;
x_26 = x_20;
goto block_30;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = x_16;
x_26 = x_20;
goto block_30;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_usize_of_nat(x_15);
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(x_23, x_34, x_35, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_23);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_25 = x_37;
x_26 = x_38;
goto block_30;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_array_to_list(x_25);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_21)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_21;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_apply_1(x_2, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_apply_1(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed), 1, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
x_15 = l_Functor_mapRev___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__5___redArg(x_14, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("repeat'", 7, 7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lean_Elab_Tactic_getGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw), 11, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = lean_unsigned_to_nat(100000u);
lean_inc(x_3);
x_29 = l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0(x_27, x_25, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_setGoals___redArg(x_30, x_3, x_31);
lean_dec(x_3);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__0(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("repeat'", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalRepeat'", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat_x27), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalRepeat'", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(13u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(17u);
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
x_16 = lean_unsigned_to_nat(15u);
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
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___Lean_Elab_Tactic_evalRepeat1_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat_x27___at___Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_mk_string_unchecked("repeat1' made no progress", 25, 25);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_19, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRepeat1_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("repeat1'", 8, 8);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lean_Elab_Tactic_getGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAtRaw), 11, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = lean_unsigned_to_nat(100000u);
lean_inc(x_3);
x_29 = l_Lean_Meta_repeat1_x27___at___Lean_Elab_Tactic_evalRepeat1_x27_spec__0(x_27, x_25, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_setGoals___redArg(x_30, x_3, x_31);
lean_dec(x_3);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("repeat1'", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalRepeat1'", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRepeat1_x27), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalRepeat1'", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(20u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(24u);
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
x_16 = lean_unsigned_to_nat(16u);
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
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
