// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize
// Imports: Lean.Elab.Tactic.FalseOrByContra Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ApplyControlFlow Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Simproc Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Rewrite Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AndFlatten Lean.Elab.Tactic.BVDecide.Frontend.Normalize.EmbeddedConstraint Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AC Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Structures Lean.Elab.Tactic.BVDecide.Frontend.Normalize.IntToBitVec Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Enums Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ShortCircuit
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_enumsPass;
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_mvarId_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize__1(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass;
x_4 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_22 == 0)
{
x_14 = x_21;
x_15 = x_2;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_25 = l_List_appendTR(lean_box(0), x_21, x_24);
x_14 = x_25;
x_15 = x_2;
goto block_20;
}
block_13:
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = l_List_appendTR(lean_box(0), x_5, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
block_20:
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_16 == 0)
{
x_5 = x_14;
x_6 = x_15;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_List_appendTR(lean_box(0), x_14, x_18);
x_5 = x_19;
x_6 = x_15;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_mk_string_unchecked("Running pass: ", 14, 14);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(" on\n", 4, 4);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_mk_string_unchecked("Running pass: ", 14, 14);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(" on\n", 4, 4);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_MVarId_falseOrByContra(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("bv", 2, 2);
x_19 = l_Lean_Name_mkStr3(x_16, x_17, x_18);
lean_inc(x_19);
x_177 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(x_19, x_6, x_12);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_166 = x_14;
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_180;
goto block_176;
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_177);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_177, 1);
x_183 = lean_ctor_get(x_177, 0);
lean_dec(x_183);
x_184 = lean_mk_string_unchecked("Running preprocessing pipeline on:\n", 35, 35);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
lean_inc(x_14);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_14);
lean_ctor_set_tag(x_177, 7);
lean_ctor_set(x_177, 1, x_186);
lean_ctor_set(x_177, 0, x_185);
x_187 = lean_mk_string_unchecked("", 0, 0);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_19);
x_190 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_19, x_189, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_166 = x_14;
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_191;
goto block_176;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_192 = lean_ctor_get(x_177, 1);
lean_inc(x_192);
lean_dec(x_177);
x_193 = lean_mk_string_unchecked("Running preprocessing pipeline on:\n", 35, 35);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
lean_inc(x_14);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_14);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_mk_string_unchecked("", 0, 0);
x_198 = l_Lean_stringToMessageData(x_197);
lean_dec(x_197);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
lean_inc(x_19);
x_200 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_19, x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_192);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_166 = x_14;
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_201;
goto block_176;
}
}
block_43:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_passPipeline___redArg(x_22, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_32 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(x_30, x_20, x_22, x_23, x_24, x_25, x_26, x_27, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
return x_32;
}
else
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 9);
lean_dec(x_21);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass;
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0___boxed), 10, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_apply_1(x_39, x_36);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(x_19, x_38, x_40, x_34, x_41, x_22, x_23, x_24, x_25, x_26, x_27, x_35);
return x_42;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
return x_32;
}
}
block_78:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_19);
x_53 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(x_19, x_50, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_15);
lean_dec(x_13);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = x_49;
x_26 = x_50;
x_27 = x_51;
x_28 = x_56;
goto block_43;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_53, 1);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
x_60 = lean_mk_string_unchecked("Running fixpoint pipeline on:\n", 30, 30);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
lean_inc(x_45);
if (lean_is_scalar(x_15)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_15;
}
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_61);
x_63 = lean_mk_string_unchecked("", 0, 0);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
if (lean_is_scalar(x_13)) {
 x_65 = lean_alloc_ctor(7, 2, 0);
} else {
 x_65 = x_13;
 lean_ctor_set_tag(x_65, 7);
}
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_19);
x_66 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_19, x_65, x_46, x_47, x_48, x_49, x_50, x_51, x_58);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = x_49;
x_26 = x_50;
x_27 = x_51;
x_28 = x_67;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec(x_53);
x_69 = lean_mk_string_unchecked("Running fixpoint pipeline on:\n", 30, 30);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
lean_inc(x_45);
if (lean_is_scalar(x_15)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_15;
}
lean_ctor_set(x_71, 0, x_45);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
if (lean_is_scalar(x_13)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_13;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_19);
x_76 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_19, x_75, x_46, x_47, x_48, x_49, x_50, x_51, x_68);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_20 = x_45;
x_21 = x_44;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = x_49;
x_26 = x_50;
x_27 = x_51;
x_28 = x_77;
goto block_43;
}
}
}
block_98:
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_79, sizeof(void*)*2 + 6);
if (x_88 == 0)
{
x_44 = x_79;
x_45 = x_80;
x_46 = x_81;
x_47 = x_82;
x_48 = x_83;
x_49 = x_84;
x_50 = x_85;
x_51 = x_86;
x_52 = x_87;
goto block_78;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass;
lean_inc(x_80);
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(x_90, 0, x_89);
lean_closure_set(x_90, 1, x_80);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = lean_apply_1(x_91, x_80);
x_93 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_19);
x_94 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(x_19, x_90, x_92, x_88, x_93, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_44 = x_79;
x_45 = x_97;
x_46 = x_81;
x_47 = x_82;
x_48 = x_83;
x_49 = x_84;
x_50 = x_85;
x_51 = x_86;
x_52 = x_96;
goto block_78;
}
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_94;
}
}
}
block_118:
{
uint8_t x_108; 
x_108 = lean_ctor_get_uint8(x_99, sizeof(void*)*2 + 7);
if (x_108 == 0)
{
x_79 = x_99;
x_80 = x_100;
x_81 = x_101;
x_82 = x_102;
x_83 = x_103;
x_84 = x_104;
x_85 = x_105;
x_86 = x_106;
x_87 = x_107;
goto block_98;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_enumsPass;
lean_inc(x_100);
x_110 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(x_110, 0, x_109);
lean_closure_set(x_110, 1, x_100);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = lean_apply_1(x_111, x_100);
x_113 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_19);
x_114 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(x_19, x_110, x_112, x_108, x_113, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_79 = x_99;
x_80 = x_117;
x_81 = x_101;
x_82 = x_102;
x_83 = x_103;
x_84 = x_104;
x_85 = x_105;
x_86 = x_106;
x_87 = x_116;
goto block_98;
}
}
else
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_114;
}
}
}
block_138:
{
uint8_t x_128; 
x_128 = lean_ctor_get_uint8(x_119, sizeof(void*)*2 + 5);
if (x_128 == 0)
{
x_99 = x_119;
x_100 = x_120;
x_101 = x_121;
x_102 = x_122;
x_103 = x_123;
x_104 = x_124;
x_105 = x_125;
x_106 = x_126;
x_107 = x_127;
goto block_118;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass;
lean_inc(x_120);
x_130 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(x_130, 0, x_129);
lean_closure_set(x_130, 1, x_120);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
x_132 = lean_apply_1(x_131, x_120);
x_133 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_19);
x_134 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(x_19, x_130, x_132, x_128, x_133, x_121, x_122, x_123, x_124, x_125, x_126, x_127);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
x_99 = x_119;
x_100 = x_137;
x_101 = x_121;
x_102 = x_122;
x_103 = x_123;
x_104 = x_124;
x_105 = x_125;
x_106 = x_126;
x_107 = x_136;
goto block_118;
}
}
else
{
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_134;
}
}
}
block_165:
{
if (x_147 == 0)
{
lean_inc(x_142);
x_119 = x_142;
x_120 = x_141;
x_121 = x_142;
x_122 = x_144;
x_123 = x_143;
x_124 = x_146;
x_125 = x_140;
x_126 = x_139;
x_127 = x_145;
goto block_138;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass;
lean_inc(x_141);
x_149 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(x_149, 0, x_148);
lean_closure_set(x_149, 1, x_141);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
x_151 = lean_apply_1(x_150, x_141);
x_152 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_139);
lean_inc(x_140);
lean_inc(x_146);
lean_inc(x_143);
lean_inc(x_144);
lean_inc(x_142);
lean_inc(x_19);
x_153 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(x_19, x_149, x_151, x_147, x_152, x_142, x_144, x_143, x_146, x_140, x_139, x_145);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_157 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_158 = lean_unsigned_to_nat(21u);
x_159 = lean_unsigned_to_nat(14u);
x_160 = lean_mk_string_unchecked("value is none", 13, 13);
x_161 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_156, x_157, x_158, x_159, x_160);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
x_162 = l_panic___at___Lean_Expr_mvarId_x21_spec__0(x_161);
lean_inc(x_142);
x_119 = x_142;
x_120 = x_162;
x_121 = x_142;
x_122 = x_144;
x_123 = x_143;
x_124 = x_146;
x_125 = x_140;
x_126 = x_139;
x_127 = x_155;
goto block_138;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_153, 1);
lean_inc(x_163);
lean_dec(x_153);
x_164 = lean_ctor_get(x_154, 0);
lean_inc(x_164);
lean_dec(x_154);
lean_inc(x_142);
x_119 = x_142;
x_120 = x_164;
x_121 = x_142;
x_122 = x_144;
x_123 = x_143;
x_124 = x_146;
x_125 = x_140;
x_126 = x_139;
x_127 = x_163;
goto block_138;
}
}
else
{
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_153;
}
}
}
block_176:
{
uint8_t x_174; 
x_174 = lean_ctor_get_uint8(x_167, sizeof(void*)*2 + 5);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_167, sizeof(void*)*2 + 7);
x_139 = x_172;
x_140 = x_171;
x_141 = x_166;
x_142 = x_167;
x_143 = x_169;
x_144 = x_168;
x_145 = x_173;
x_146 = x_170;
x_147 = x_175;
goto block_165;
}
else
{
x_139 = x_172;
x_140 = x_171;
x_141 = x_166;
x_142 = x_167;
x_143 = x_169;
x_144 = x_168;
x_145 = x_173;
x_146 = x_170;
x_147 = x_174;
goto block_165;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Preprocessing goal", 18, 18);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getPropHyps), 5, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_10);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_shiftl(x_12, x_14);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
x_18 = l_Nat_nextPowerOfTwo(x_17);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(8u);
x_23 = lean_nat_shiftl(x_22, x_14);
x_24 = lean_nat_div(x_23, x_16);
lean_dec(x_23);
x_25 = l_Nat_nextPowerOfTwo(x_24);
lean_dec(x_24);
x_26 = lean_mk_array(x_25, x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
lean_inc_n(x_27, 3);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_27);
lean_inc(x_21);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_st_mk_ref(x_29, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize_go(x_1, x_2, x_31, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_dec(x_31);
return x_33;
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
return x_9;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0___boxed), 6, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__1), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_mk_string_unchecked("bv", 2, 2);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_8, x_9, x_16, x_15, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("bvNormalize", 11, 11);
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
x_20 = lean_mk_string_unchecked("optConfig", 9, 9);
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
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_19, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(x_28, x_25, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_33, x_3, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_38, x_3, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
return x_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("bvNormalize", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_10 = lean_mk_string_unchecked("Frontend", 8, 8);
x_11 = lean_mk_string_unchecked("Normalize", 9, 9);
x_12 = lean_mk_string_unchecked("evalBVNormalize", 15, 15);
x_13 = l_Lean_Name_mkStr7(x_3, x_8, x_5, x_9, x_10, x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize___boxed), 10, 0);
x_15 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_13, x_14, x_1);
return x_15;
}
}
lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AndFlatten(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Enums(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AndFlatten(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Enums(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_evalBVNormalize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
