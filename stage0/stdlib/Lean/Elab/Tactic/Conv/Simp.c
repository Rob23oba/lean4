// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Simp
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv.Basic Lean.Elab.Tactic.SimpTrace
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
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_Conv_changeLhs(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_Meta_Simp_Result_getProof(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Elab_Tactic_Conv_updateLhs(x_17, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_unsigned_to_nat(5u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_nat_pow(x_19, x_22);
lean_dec(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set_usize(x_28, 4, x_21);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_18);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_simp(x_1, x_2, x_3, x_4, x_30, x_9, x_10, x_11, x_12, x_13);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Elab_Tactic_Conv_getLhs(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed), 13, 3);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_19, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalSimp", 8, 8);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("Conv", 4, 4);
x_6 = lean_mk_string_unchecked("evalSimp", 8, 8);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(20u);
x_9 = lean_unsigned_to_nat(47u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(24u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(51u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(59u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_7, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_unsigned_to_nat(5u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_nat_pow(x_2, x_22);
lean_dec(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_1);
x_28 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_1);
lean_ctor_set_usize(x_28, 4, x_21);
lean_inc(x_17);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_simp(x_3, x_4, x_5, x_6, x_30, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(2u);
x_234 = l_Lean_Syntax_getArg(x_2, x_24);
x_277 = lean_unsigned_to_nat(3u);
x_278 = l_Lean_Syntax_getArg(x_2, x_277);
x_279 = l_Lean_Syntax_isNone(x_278);
if (x_279 == 0)
{
uint8_t x_280; 
lean_inc(x_278);
x_280 = l_Lean_Syntax_matchesNull(x_278, x_17);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_278);
lean_dec(x_234);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_281 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = l_Lean_Syntax_getArg(x_278, x_23);
lean_dec(x_278);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_252 = x_283;
x_253 = x_7;
x_254 = x_8;
x_255 = x_9;
x_256 = x_10;
x_257 = x_11;
x_258 = x_12;
x_259 = x_13;
x_260 = x_14;
x_261 = x_15;
goto block_276;
}
}
else
{
lean_object* x_284; 
lean_dec(x_278);
x_284 = lean_box(0);
x_252 = x_284;
x_253 = x_7;
x_254 = x_8;
x_255 = x_9;
x_256 = x_10;
x_257 = x_11;
x_258 = x_12;
x_259 = x_13;
x_260 = x_14;
x_261 = x_15;
goto block_276;
}
block_121:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
lean_inc(x_34);
x_45 = l_Array_append(lean_box(0), x_34, x_44);
lean_dec(x_44);
lean_inc(x_28);
lean_inc(x_32);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_28);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_32);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_28);
lean_ctor_set(x_47, 2, x_34);
x_48 = l_Lean_Syntax_node6(x_32, x_41, x_40, x_18, x_25, x_33, x_46, x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_51 = lean_unbox(x_49);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_42);
lean_inc(x_30);
lean_inc(x_36);
lean_inc(x_37);
lean_inc(x_35);
x_52 = l_Lean_Elab_Tactic_mkSimpContext(x_48, x_38, x_51, x_38, x_50, x_35, x_37, x_36, x_30, x_42, x_26, x_27, x_29, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 2);
lean_inc(x_57);
lean_dec(x_53);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
x_58 = l_Lean_Elab_Tactic_Conv_getLhs(x_35, x_37, x_36, x_30, x_42, x_26, x_27, x_29, x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed), 15, 5);
lean_closure_set(x_61, 0, x_23);
lean_closure_set(x_61, 1, x_24);
lean_closure_set(x_61, 2, x_59);
lean_closure_set(x_61, 3, x_55);
lean_closure_set(x_61, 4, x_56);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_42);
lean_inc(x_30);
lean_inc(x_36);
lean_inc(x_37);
lean_inc(x_35);
x_62 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_57, x_61, x_35, x_37, x_36, x_30, x_42, x_26, x_27, x_29, x_60);
lean_dec(x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_42);
x_67 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_65, x_35, x_37, x_36, x_30, x_42, x_26, x_27, x_29, x_64);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_42);
x_72 = l_Lean_Elab_Tactic_mkSimpCallStx(x_48, x_71, x_42, x_26, x_27, x_29, x_69);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_mk_string_unchecked("tactic", 6, 6);
x_76 = l_Lean_Name_mkStr1(x_75);
lean_ctor_set(x_67, 1, x_73);
lean_ctor_set(x_67, 0, x_76);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = lean_box(0);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_77);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_43);
x_83 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_84 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_31, x_81, x_82, x_83, x_77, x_42, x_26, x_27, x_29, x_74);
lean_dec(x_26);
lean_dec(x_42);
lean_dec(x_82);
lean_dec(x_31);
return x_84;
}
else
{
uint8_t x_85; 
lean_free_object(x_67);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
return x_72;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_72, 0);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_72);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
lean_dec(x_67);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
lean_dec(x_66);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_42);
x_91 = l_Lean_Elab_Tactic_mkSimpCallStx(x_48, x_90, x_42, x_26, x_27, x_29, x_89);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_mk_string_unchecked("tactic", 6, 6);
x_95 = l_Lean_Name_mkStr1(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
x_97 = lean_box(0);
x_98 = lean_box(0);
x_99 = lean_box(0);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_97);
lean_ctor_set(x_101, 3, x_98);
lean_ctor_set(x_101, 4, x_99);
lean_ctor_set(x_101, 5, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
x_103 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_104 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_31, x_101, x_102, x_103, x_97, x_42, x_26, x_27, x_29, x_93);
lean_dec(x_26);
lean_dec(x_42);
lean_dec(x_102);
lean_dec(x_31);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_105 = lean_ctor_get(x_91, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_91, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_107 = x_91;
} else {
 lean_dec_ref(x_91);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
return x_67;
}
}
else
{
uint8_t x_109; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_109 = !lean_is_exclusive(x_62);
if (x_109 == 0)
{
return x_62;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_62, 0);
x_111 = lean_ctor_get(x_62, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_62);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_113 = !lean_is_exclusive(x_58);
if (x_113 == 0)
{
return x_58;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_58, 0);
x_115 = lean_ctor_get(x_58, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_58);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_117 = !lean_is_exclusive(x_52);
if (x_117 == 0)
{
return x_52;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_52, 0);
x_119 = lean_ctor_get(x_52, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_52);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
block_153:
{
lean_object* x_142; lean_object* x_143; 
lean_inc(x_131);
x_142 = l_Array_append(lean_box(0), x_131, x_141);
lean_dec(x_141);
lean_inc(x_125);
lean_inc(x_130);
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_125);
lean_ctor_set(x_143, 2, x_142);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_144; 
x_144 = l_Array_empty(lean_box(0));
x_25 = x_122;
x_26 = x_123;
x_27 = x_126;
x_28 = x_125;
x_29 = x_127;
x_30 = x_128;
x_31 = x_129;
x_32 = x_130;
x_33 = x_143;
x_34 = x_131;
x_35 = x_132;
x_36 = x_133;
x_37 = x_134;
x_38 = x_135;
x_39 = x_136;
x_40 = x_137;
x_41 = x_138;
x_42 = x_139;
x_43 = x_140;
x_44 = x_144;
goto block_121;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_124, 0);
lean_inc(x_145);
lean_dec(x_124);
x_146 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_130);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_130);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_131);
x_148 = l_Array_append(lean_box(0), x_131, x_145);
lean_dec(x_145);
lean_inc(x_125);
lean_inc(x_130);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_130);
lean_ctor_set(x_149, 1, x_125);
lean_ctor_set(x_149, 2, x_148);
x_150 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_130);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_130);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Array_mkArray3(lean_box(0), x_147, x_149, x_151);
x_25 = x_122;
x_26 = x_123;
x_27 = x_126;
x_28 = x_125;
x_29 = x_127;
x_30 = x_128;
x_31 = x_129;
x_32 = x_130;
x_33 = x_143;
x_34 = x_131;
x_35 = x_132;
x_36 = x_133;
x_37 = x_134;
x_38 = x_135;
x_39 = x_136;
x_40 = x_137;
x_41 = x_138;
x_42 = x_139;
x_43 = x_140;
x_44 = x_152;
goto block_121;
}
}
block_182:
{
lean_object* x_174; lean_object* x_175; 
lean_inc(x_163);
x_174 = l_Array_append(lean_box(0), x_163, x_173);
lean_dec(x_173);
lean_inc(x_155);
lean_inc(x_162);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_162);
lean_ctor_set(x_175, 1, x_155);
lean_ctor_set(x_175, 2, x_174);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_176; 
x_176 = l_Array_empty(lean_box(0));
x_122 = x_175;
x_123 = x_154;
x_124 = x_156;
x_125 = x_155;
x_126 = x_157;
x_127 = x_158;
x_128 = x_159;
x_129 = x_161;
x_130 = x_162;
x_131 = x_163;
x_132 = x_164;
x_133 = x_165;
x_134 = x_166;
x_135 = x_167;
x_136 = x_168;
x_137 = x_169;
x_138 = x_170;
x_139 = x_171;
x_140 = x_172;
x_141 = x_176;
goto block_153;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_160, 0);
lean_inc(x_177);
lean_dec(x_160);
x_178 = l_Lean_SourceInfo_fromRef(x_177, x_6);
lean_dec(x_177);
x_179 = lean_mk_string_unchecked("only", 4, 4);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Array_mkArray1___redArg(x_180);
x_122 = x_175;
x_123 = x_154;
x_124 = x_156;
x_125 = x_155;
x_126 = x_157;
x_127 = x_158;
x_128 = x_159;
x_129 = x_161;
x_130 = x_162;
x_131 = x_163;
x_132 = x_164;
x_133 = x_165;
x_134 = x_166;
x_135 = x_167;
x_136 = x_168;
x_137 = x_169;
x_138 = x_170;
x_139 = x_171;
x_140 = x_172;
x_141 = x_181;
goto block_153;
}
}
block_233:
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_st_ref_get(x_187, x_190);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_197 = lean_ctor_get(x_195, 1);
x_198 = lean_ctor_get(x_195, 0);
lean_dec(x_198);
x_199 = lean_ctor_get(x_186, 5);
lean_inc(x_199);
x_200 = lean_box(0);
x_201 = l_Lean_Syntax_getArg(x_2, x_23);
x_202 = lean_unbox(x_200);
x_203 = l_Lean_SourceInfo_fromRef(x_199, x_202);
x_204 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_204);
x_205 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_204);
x_206 = l_Lean_SourceInfo_fromRef(x_201, x_6);
lean_ctor_set_tag(x_195, 2);
lean_ctor_set(x_195, 1, x_204);
lean_ctor_set(x_195, 0, x_206);
x_207 = lean_mk_string_unchecked("null", 4, 4);
x_208 = l_Lean_Name_mkStr1(x_207);
x_209 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = l_Array_empty(lean_box(0));
x_211 = lean_unbox(x_200);
x_154 = x_184;
x_155 = x_208;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_201;
x_162 = x_203;
x_163 = x_209;
x_164 = x_193;
x_165 = x_192;
x_166 = x_183;
x_167 = x_211;
x_168 = x_197;
x_169 = x_195;
x_170 = x_205;
x_171 = x_191;
x_172 = x_199;
x_173 = x_210;
goto block_182;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_194, 0);
lean_inc(x_212);
lean_dec(x_194);
x_213 = l_Array_mkArray1___redArg(x_212);
x_214 = lean_unbox(x_200);
x_154 = x_184;
x_155 = x_208;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_201;
x_162 = x_203;
x_163 = x_209;
x_164 = x_193;
x_165 = x_192;
x_166 = x_183;
x_167 = x_214;
x_168 = x_197;
x_169 = x_195;
x_170 = x_205;
x_171 = x_191;
x_172 = x_199;
x_173 = x_213;
goto block_182;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_dec(x_195);
x_216 = lean_ctor_get(x_186, 5);
lean_inc(x_216);
x_217 = lean_box(0);
x_218 = l_Lean_Syntax_getArg(x_2, x_23);
x_219 = lean_unbox(x_217);
x_220 = l_Lean_SourceInfo_fromRef(x_216, x_219);
x_221 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_221);
x_222 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_221);
x_223 = l_Lean_SourceInfo_fromRef(x_218, x_6);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
x_225 = lean_mk_string_unchecked("null", 4, 4);
x_226 = l_Lean_Name_mkStr1(x_225);
x_227 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = l_Array_empty(lean_box(0));
x_229 = lean_unbox(x_217);
x_154 = x_184;
x_155 = x_226;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_218;
x_162 = x_220;
x_163 = x_227;
x_164 = x_193;
x_165 = x_192;
x_166 = x_183;
x_167 = x_229;
x_168 = x_215;
x_169 = x_224;
x_170 = x_222;
x_171 = x_191;
x_172 = x_216;
x_173 = x_228;
goto block_182;
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_194, 0);
lean_inc(x_230);
lean_dec(x_194);
x_231 = l_Array_mkArray1___redArg(x_230);
x_232 = lean_unbox(x_217);
x_154 = x_184;
x_155 = x_226;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_218;
x_162 = x_220;
x_163 = x_227;
x_164 = x_193;
x_165 = x_192;
x_166 = x_183;
x_167 = x_232;
x_168 = x_215;
x_169 = x_224;
x_170 = x_222;
x_171 = x_191;
x_172 = x_216;
x_173 = x_231;
goto block_182;
}
}
}
block_251:
{
lean_object* x_246; 
x_246 = l_Lean_Syntax_getOptional_x3f(x_234);
lean_dec(x_234);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_183 = x_238;
x_184 = x_242;
x_185 = x_236;
x_186 = x_243;
x_187 = x_244;
x_188 = x_240;
x_189 = x_235;
x_190 = x_245;
x_191 = x_241;
x_192 = x_239;
x_193 = x_237;
x_194 = x_247;
goto block_233;
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_246);
if (x_248 == 0)
{
x_183 = x_238;
x_184 = x_242;
x_185 = x_236;
x_186 = x_243;
x_187 = x_244;
x_188 = x_240;
x_189 = x_235;
x_190 = x_245;
x_191 = x_241;
x_192 = x_239;
x_193 = x_237;
x_194 = x_246;
goto block_233;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_183 = x_238;
x_184 = x_242;
x_185 = x_236;
x_186 = x_243;
x_187 = x_244;
x_188 = x_240;
x_189 = x_235;
x_190 = x_245;
x_191 = x_241;
x_192 = x_239;
x_193 = x_237;
x_194 = x_250;
goto block_233;
}
}
}
block_276:
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_unsigned_to_nat(4u);
x_263 = l_Lean_Syntax_getArg(x_2, x_262);
x_264 = l_Lean_Syntax_isNone(x_263);
if (x_264 == 0)
{
uint8_t x_265; 
lean_inc(x_263);
x_265 = l_Lean_Syntax_matchesNull(x_263, x_17);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_234);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_266 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_261);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = l_Lean_Syntax_getArg(x_263, x_23);
lean_dec(x_263);
x_268 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_269 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_268);
lean_inc(x_267);
x_270 = l_Lean_Syntax_isOfKind(x_267, x_269);
lean_dec(x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_267);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_234);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_271 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_261);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = l_Lean_Syntax_getArg(x_267, x_17);
lean_dec(x_267);
x_273 = l_Lean_Syntax_getArgs(x_272);
lean_dec(x_272);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_235 = x_252;
x_236 = x_274;
x_237 = x_253;
x_238 = x_254;
x_239 = x_255;
x_240 = x_256;
x_241 = x_257;
x_242 = x_258;
x_243 = x_259;
x_244 = x_260;
x_245 = x_261;
goto block_251;
}
}
}
else
{
lean_object* x_275; 
lean_dec(x_263);
x_275 = lean_box(0);
x_235 = x_252;
x_236 = x_275;
x_237 = x_253;
x_238 = x_254;
x_239 = x_255;
x_240 = x_256;
x_241 = x_257;
x_242 = x_258;
x_243 = x_259;
x_244 = x_260;
x_245 = x_261;
goto block_251;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("Conv", 4, 4);
x_15 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_Name_mkStr5(x_11, x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed), 15, 6);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_11);
lean_closure_set(x_20, 3, x_12);
lean_closure_set(x_20, 4, x_13);
lean_closure_set(x_20, 5, x_18);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalSimpTrace", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_Split_simpMatch(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0), 9, 0);
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSimpMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("simpMatch", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalSimpMatch", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("Conv", 4, 4);
x_6 = lean_mk_string_unchecked("evalSimpMatch", 13, 13);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(26u);
x_9 = lean_unsigned_to_nat(52u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(27u);
x_12 = lean_unsigned_to_nat(48u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(56u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(69u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Elab_Tactic_Conv_getLhs(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_nat_pow(x_27, x_30);
lean_dec(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_21);
lean_ctor_set_usize(x_36, 4, x_29);
lean_inc(x_24);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_39 = l_Lean_Meta_dsimp(x_19, x_17, x_22, x_38, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Tactic_Conv_changeLhs(x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_41);
lean_dec(x_9);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_box(2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed), 13, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalDSimp", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("Conv", 4, 4);
x_6 = lean_mk_string_unchecked("evalDSimp", 9, 9);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(29u);
x_9 = lean_unsigned_to_nat(48u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_9);
x_14 = lean_unsigned_to_nat(52u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(61u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_7, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_23 = lean_unsigned_to_nat(0u);
x_249 = lean_unsigned_to_nat(2u);
x_250 = l_Lean_Syntax_getArg(x_2, x_249);
x_251 = l_Lean_Syntax_isNone(x_250);
if (x_251 == 0)
{
uint8_t x_252; 
lean_inc(x_250);
x_252 = l_Lean_Syntax_matchesNull(x_250, x_17);
if (x_252 == 0)
{
lean_object* x_253; 
lean_dec(x_250);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_253 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = l_Lean_Syntax_getArg(x_250, x_23);
lean_dec(x_250);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
x_224 = x_255;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_11;
x_230 = x_12;
x_231 = x_13;
x_232 = x_14;
x_233 = x_15;
goto block_248;
}
}
else
{
lean_object* x_256; 
lean_dec(x_250);
x_256 = lean_box(0);
x_224 = x_256;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_11;
x_230 = x_12;
x_231 = x_13;
x_232 = x_14;
x_233 = x_15;
goto block_248;
}
block_133:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_44 = l_Array_append(lean_box(0), x_29, x_43);
lean_dec(x_43);
lean_inc(x_27);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_35);
x_46 = l_Lean_Syntax_node6(x_27, x_41, x_32, x_18, x_35, x_37, x_45, x_35);
x_47 = lean_box(2);
x_48 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_49 = lean_unbox(x_47);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
lean_inc(x_39);
lean_inc(x_42);
lean_inc(x_34);
lean_inc(x_30);
lean_inc(x_25);
x_50 = l_Lean_Elab_Tactic_mkSimpContext(x_46, x_26, x_49, x_26, x_48, x_25, x_30, x_34, x_42, x_39, x_28, x_38, x_33, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
x_54 = l_Lean_Elab_Tactic_Conv_getLhs(x_25, x_30, x_34, x_42, x_39, x_28, x_38, x_33, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_mk_empty_array_with_capacity(x_23);
x_58 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_58);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_23);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_unsigned_to_nat(5u);
x_64 = lean_usize_of_nat(x_63);
x_65 = lean_usize_to_nat(x_64);
x_66 = lean_nat_pow(x_62, x_65);
lean_dec(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = lean_usize_to_nat(x_67);
x_69 = lean_mk_empty_array_with_capacity(x_68);
lean_dec(x_68);
lean_inc(x_69);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_23);
lean_ctor_set(x_71, 3, x_23);
lean_ctor_set_usize(x_71, 4, x_64);
lean_inc(x_59);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_61);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
lean_inc(x_39);
x_74 = l_Lean_Meta_dsimp(x_55, x_53, x_57, x_73, x_39, x_28, x_38, x_33, x_56);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
x_79 = l_Lean_Elab_Tactic_Conv_changeLhs(x_77, x_25, x_30, x_34, x_42, x_39, x_28, x_38, x_33, x_76);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_79, 1);
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec(x_78);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
lean_inc(x_39);
x_84 = l_Lean_Elab_Tactic_mkSimpCallStx(x_46, x_83, x_39, x_28, x_38, x_33, x_81);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_mk_string_unchecked("tactic", 6, 6);
x_88 = l_Lean_Name_mkStr1(x_87);
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_88);
x_89 = lean_box(0);
x_90 = lean_box(0);
x_91 = lean_box(0);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_79);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_90);
lean_ctor_set(x_93, 4, x_91);
lean_ctor_set(x_93, 5, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_31);
x_95 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_96 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_24, x_93, x_94, x_95, x_89, x_39, x_28, x_38, x_33, x_86);
lean_dec(x_28);
lean_dec(x_39);
lean_dec(x_94);
lean_dec(x_24);
return x_96;
}
else
{
uint8_t x_97; 
lean_free_object(x_79);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
return x_84;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_84, 0);
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_84);
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
x_101 = lean_ctor_get(x_79, 1);
lean_inc(x_101);
lean_dec(x_79);
x_102 = lean_ctor_get(x_78, 0);
lean_inc(x_102);
lean_dec(x_78);
lean_inc(x_33);
lean_inc(x_38);
lean_inc(x_28);
lean_inc(x_39);
x_103 = l_Lean_Elab_Tactic_mkSimpCallStx(x_46, x_102, x_39, x_28, x_38, x_33, x_101);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("tactic", 6, 6);
x_107 = l_Lean_Name_mkStr1(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_109 = lean_box(0);
x_110 = lean_box(0);
x_111 = lean_box(0);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_109);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_111);
lean_ctor_set(x_113, 5, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_31);
x_115 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_116 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_24, x_113, x_114, x_115, x_109, x_39, x_28, x_38, x_33, x_105);
lean_dec(x_28);
lean_dec(x_39);
lean_dec(x_114);
lean_dec(x_24);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
x_117 = lean_ctor_get(x_103, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_119 = x_103;
} else {
 lean_dec_ref(x_103);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
lean_dec(x_78);
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
return x_79;
}
}
else
{
uint8_t x_121; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_121 = !lean_is_exclusive(x_74);
if (x_121 == 0)
{
return x_74;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_74, 0);
x_123 = lean_ctor_get(x_74, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_74);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_53);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_125 = !lean_is_exclusive(x_54);
if (x_125 == 0)
{
return x_54;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_54, 0);
x_127 = lean_ctor_get(x_54, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_54);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_129 = !lean_is_exclusive(x_50);
if (x_129 == 0)
{
return x_50;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_50, 0);
x_131 = lean_ctor_get(x_50, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_50);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
block_165:
{
lean_object* x_154; lean_object* x_155; 
lean_inc(x_139);
x_154 = l_Array_append(lean_box(0), x_139, x_153);
lean_dec(x_153);
lean_inc(x_152);
lean_inc(x_137);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_137);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set(x_155, 2, x_154);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_156; 
x_156 = l_Array_empty(lean_box(0));
x_24 = x_134;
x_25 = x_135;
x_26 = x_136;
x_27 = x_137;
x_28 = x_138;
x_29 = x_139;
x_30 = x_140;
x_31 = x_141;
x_32 = x_143;
x_33 = x_144;
x_34 = x_145;
x_35 = x_146;
x_36 = x_147;
x_37 = x_155;
x_38 = x_148;
x_39 = x_149;
x_40 = x_152;
x_41 = x_151;
x_42 = x_150;
x_43 = x_156;
goto block_133;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_142, 0);
lean_inc(x_157);
lean_dec(x_142);
x_158 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_137);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_137);
lean_ctor_set(x_159, 1, x_158);
lean_inc(x_139);
x_160 = l_Array_append(lean_box(0), x_139, x_157);
lean_dec(x_157);
lean_inc(x_152);
lean_inc(x_137);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_137);
lean_ctor_set(x_161, 1, x_152);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_137);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_137);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Array_mkArray3(lean_box(0), x_159, x_161, x_163);
x_24 = x_134;
x_25 = x_135;
x_26 = x_136;
x_27 = x_137;
x_28 = x_138;
x_29 = x_139;
x_30 = x_140;
x_31 = x_141;
x_32 = x_143;
x_33 = x_144;
x_34 = x_145;
x_35 = x_146;
x_36 = x_147;
x_37 = x_155;
x_38 = x_148;
x_39 = x_149;
x_40 = x_152;
x_41 = x_151;
x_42 = x_150;
x_43 = x_164;
goto block_133;
}
}
block_223:
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_st_ref_get(x_175, x_176);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_179 = lean_ctor_get(x_177, 1);
x_180 = lean_ctor_get(x_177, 0);
lean_dec(x_180);
x_181 = lean_ctor_get(x_174, 5);
lean_inc(x_181);
x_182 = lean_box(0);
x_183 = l_Lean_Syntax_getArg(x_2, x_23);
x_184 = lean_unbox(x_182);
x_185 = l_Lean_SourceInfo_fromRef(x_181, x_184);
x_186 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_186);
x_187 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_186);
x_188 = l_Lean_SourceInfo_fromRef(x_183, x_6);
lean_ctor_set_tag(x_177, 2);
lean_ctor_set(x_177, 1, x_186);
lean_ctor_set(x_177, 0, x_188);
x_189 = lean_mk_string_unchecked("null", 4, 4);
x_190 = l_Lean_Name_mkStr1(x_189);
x_191 = l_Array_mkArray0(lean_box(0));
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_185);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_185);
lean_ctor_set(x_192, 1, x_190);
lean_ctor_set(x_192, 2, x_191);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = l_Array_empty(lean_box(0));
x_194 = lean_unbox(x_182);
x_134 = x_183;
x_135 = x_168;
x_136 = x_194;
x_137 = x_185;
x_138 = x_173;
x_139 = x_191;
x_140 = x_169;
x_141 = x_181;
x_142 = x_167;
x_143 = x_177;
x_144 = x_175;
x_145 = x_170;
x_146 = x_192;
x_147 = x_179;
x_148 = x_174;
x_149 = x_172;
x_150 = x_171;
x_151 = x_187;
x_152 = x_190;
x_153 = x_193;
goto block_165;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_166, 0);
lean_inc(x_195);
lean_dec(x_166);
x_196 = l_Lean_SourceInfo_fromRef(x_195, x_6);
lean_dec(x_195);
x_197 = lean_mk_string_unchecked("only", 4, 4);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Array_mkArray1___redArg(x_198);
x_200 = lean_unbox(x_182);
x_134 = x_183;
x_135 = x_168;
x_136 = x_200;
x_137 = x_185;
x_138 = x_173;
x_139 = x_191;
x_140 = x_169;
x_141 = x_181;
x_142 = x_167;
x_143 = x_177;
x_144 = x_175;
x_145 = x_170;
x_146 = x_192;
x_147 = x_179;
x_148 = x_174;
x_149 = x_172;
x_150 = x_171;
x_151 = x_187;
x_152 = x_190;
x_153 = x_199;
goto block_165;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_201 = lean_ctor_get(x_177, 1);
lean_inc(x_201);
lean_dec(x_177);
x_202 = lean_ctor_get(x_174, 5);
lean_inc(x_202);
x_203 = lean_box(0);
x_204 = l_Lean_Syntax_getArg(x_2, x_23);
x_205 = lean_unbox(x_203);
x_206 = l_Lean_SourceInfo_fromRef(x_202, x_205);
x_207 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_207);
x_208 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_207);
x_209 = l_Lean_SourceInfo_fromRef(x_204, x_6);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_207);
x_211 = lean_mk_string_unchecked("null", 4, 4);
x_212 = l_Lean_Name_mkStr1(x_211);
x_213 = l_Array_mkArray0(lean_box(0));
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_206);
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_206);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_214, 2, x_213);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = l_Array_empty(lean_box(0));
x_216 = lean_unbox(x_203);
x_134 = x_204;
x_135 = x_168;
x_136 = x_216;
x_137 = x_206;
x_138 = x_173;
x_139 = x_213;
x_140 = x_169;
x_141 = x_202;
x_142 = x_167;
x_143 = x_210;
x_144 = x_175;
x_145 = x_170;
x_146 = x_214;
x_147 = x_201;
x_148 = x_174;
x_149 = x_172;
x_150 = x_171;
x_151 = x_208;
x_152 = x_212;
x_153 = x_215;
goto block_165;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_217 = lean_ctor_get(x_166, 0);
lean_inc(x_217);
lean_dec(x_166);
x_218 = l_Lean_SourceInfo_fromRef(x_217, x_6);
lean_dec(x_217);
x_219 = lean_mk_string_unchecked("only", 4, 4);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Array_mkArray1___redArg(x_220);
x_222 = lean_unbox(x_203);
x_134 = x_204;
x_135 = x_168;
x_136 = x_222;
x_137 = x_206;
x_138 = x_173;
x_139 = x_213;
x_140 = x_169;
x_141 = x_202;
x_142 = x_167;
x_143 = x_210;
x_144 = x_175;
x_145 = x_170;
x_146 = x_214;
x_147 = x_201;
x_148 = x_174;
x_149 = x_172;
x_150 = x_171;
x_151 = x_208;
x_152 = x_212;
x_153 = x_221;
goto block_165;
}
}
}
block_248:
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_unsigned_to_nat(3u);
x_235 = l_Lean_Syntax_getArg(x_2, x_234);
x_236 = l_Lean_Syntax_isNone(x_235);
if (x_236 == 0)
{
uint8_t x_237; 
lean_inc(x_235);
x_237 = l_Lean_Syntax_matchesNull(x_235, x_17);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_238 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_233);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_239 = l_Lean_Syntax_getArg(x_235, x_23);
lean_dec(x_235);
x_240 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_241 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_240);
lean_inc(x_239);
x_242 = l_Lean_Syntax_isOfKind(x_239, x_241);
lean_dec(x_241);
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec(x_239);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_243 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_233);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = l_Lean_Syntax_getArg(x_239, x_17);
lean_dec(x_239);
x_245 = l_Lean_Syntax_getArgs(x_244);
lean_dec(x_244);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_166 = x_224;
x_167 = x_246;
x_168 = x_225;
x_169 = x_226;
x_170 = x_227;
x_171 = x_228;
x_172 = x_229;
x_173 = x_230;
x_174 = x_231;
x_175 = x_232;
x_176 = x_233;
goto block_223;
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_235);
x_247 = lean_box(0);
x_166 = x_224;
x_167 = x_247;
x_168 = x_225;
x_169 = x_226;
x_170 = x_227;
x_171 = x_228;
x_172 = x_229;
x_173 = x_230;
x_174 = x_231;
x_175 = x_232;
x_176 = x_233;
goto block_223;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("Conv", 4, 4);
x_15 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_Name_mkStr5(x_11, x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_11);
lean_closure_set(x_20, 3, x_12);
lean_closure_set(x_20, 4, x_13);
lean_closure_set(x_20, 5, x_18);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("evalDSimpTrace", 14, 14);
x_11 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_11, x_12, x_1);
return x_13;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
