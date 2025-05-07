// Lean compiler output
// Module: Lean.Elab.CheckTactic
// Imports: Lean.Elab.Tactic.ElabTerm Lean.Elab.Command Lean.Elab.Tactic.Meta Lean.Meta.CheckTactic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__1(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_box(0);
x_18 = lean_box(x_2);
x_19 = lean_box(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_20, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_24);
x_26 = lean_infer_type(x_24, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_24, x_27, x_12, x_13, x_14, x_15, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = lean_unbox(x_34);
lean_inc(x_12);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_33, x_36, x_35, x_12, x_13, x_14, x_15, x_32);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_27);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l_Lean_Elab_Term_elabTerm(x_3, x_41, x_2, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_usize_of_nat(x_4);
x_52 = lean_usize_to_nat(x_51);
x_53 = lean_nat_pow(x_50, x_52);
lean_dec(x_52);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = lean_usize_to_nat(x_54);
x_56 = lean_mk_empty_array_with_capacity(x_55);
lean_dec(x_55);
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_5);
x_58 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_5);
lean_ctor_set(x_58, 3, x_5);
lean_ctor_set_usize(x_58, 4, x_51);
x_59 = lean_box(0);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_61, 4, x_59);
lean_ctor_set(x_61, 5, x_59);
lean_ctor_set(x_61, 6, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 1, x_2);
x_62 = lean_unbox(x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 2, x_62);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 4, x_2);
x_63 = lean_unbox(x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 5, x_63);
x_64 = lean_unbox(x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 6, x_64);
x_65 = lean_unbox(x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 7, x_65);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 8, x_2);
x_66 = lean_unbox(x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 9, x_66);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 10, x_2);
x_67 = lean_box(0);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_59);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_59);
lean_ctor_set(x_71, 6, x_70);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_72 = l_Lean_Elab_runTactic(x_45, x_7, x_61, x_71, x_12, x_13, x_14, x_15, x_44);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_75;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked(" closed goal, but is expected to reduce to ", 43, 43);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_82);
lean_ctor_set(x_37, 0, x_80);
x_83 = l_Lean_indentExpr(x_43);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_83);
lean_ctor_set(x_29, 0, x_37);
x_84 = lean_mk_string_unchecked(".", 1, 1);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_29);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_86, x_10, x_11, x_12, x_13, x_14, x_15, x_76);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_87;
}
else
{
lean_object* x_88; 
lean_free_object(x_29);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_37);
lean_dec(x_7);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_91 = x_74;
} else {
 lean_dec_ref(x_74);
 x_91 = lean_box(0);
}
x_92 = l_Lean_MVarId_getType(x_90, x_12, x_13, x_14, x_15, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_95 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_8, x_93, x_12, x_13, x_14, x_15, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; uint8_t x_168; uint64_t x_169; uint64_t x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_143 = lean_box(2);
x_144 = lean_ctor_get(x_12, 0);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_144, 0);
x_146 = lean_ctor_get_uint8(x_144, 1);
x_147 = lean_ctor_get_uint8(x_144, 2);
x_148 = lean_ctor_get_uint8(x_144, 3);
x_149 = lean_ctor_get_uint8(x_144, 4);
x_150 = lean_ctor_get_uint8(x_144, 5);
x_151 = lean_ctor_get_uint8(x_144, 6);
x_152 = lean_ctor_get_uint8(x_144, 7);
x_153 = lean_ctor_get_uint8(x_144, 8);
x_154 = lean_ctor_get_uint8(x_144, 10);
x_155 = lean_ctor_get_uint8(x_144, 11);
x_156 = lean_ctor_get_uint8(x_144, 12);
x_157 = lean_ctor_get_uint8(x_144, 13);
x_158 = lean_ctor_get_uint8(x_144, 14);
x_159 = lean_ctor_get_uint8(x_144, 15);
x_160 = lean_ctor_get_uint8(x_144, 16);
x_161 = lean_ctor_get_uint8(x_144, 17);
lean_dec(x_144);
x_162 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_162, 0, x_145);
lean_ctor_set_uint8(x_162, 1, x_146);
lean_ctor_set_uint8(x_162, 2, x_147);
lean_ctor_set_uint8(x_162, 3, x_148);
lean_ctor_set_uint8(x_162, 4, x_149);
lean_ctor_set_uint8(x_162, 5, x_150);
lean_ctor_set_uint8(x_162, 6, x_151);
lean_ctor_set_uint8(x_162, 7, x_152);
lean_ctor_set_uint8(x_162, 8, x_153);
x_163 = lean_unbox(x_143);
lean_ctor_set_uint8(x_162, 9, x_163);
lean_ctor_set_uint8(x_162, 10, x_154);
lean_ctor_set_uint8(x_162, 11, x_155);
lean_ctor_set_uint8(x_162, 12, x_156);
lean_ctor_set_uint8(x_162, 13, x_157);
lean_ctor_set_uint8(x_162, 14, x_158);
lean_ctor_set_uint8(x_162, 15, x_159);
lean_ctor_set_uint8(x_162, 16, x_160);
lean_ctor_set_uint8(x_162, 17, x_161);
x_164 = lean_ctor_get_uint64(x_12, sizeof(void*)*7);
x_165 = lean_uint64_of_nat(x_50);
x_166 = lean_uint64_shift_right(x_164, x_165);
x_167 = lean_uint64_shift_left(x_166, x_165);
x_168 = lean_unbox(x_143);
x_169 = l_Lean_Meta_TransparencyMode_toUInt64(x_168);
x_170 = lean_uint64_lor(x_167, x_169);
x_171 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 8);
x_172 = lean_ctor_get(x_12, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_12, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_12, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_12, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_12, 5);
lean_inc(x_176);
x_177 = lean_ctor_get(x_12, 6);
lean_inc(x_177);
x_178 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 9);
x_179 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 10);
x_180 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set(x_180, 1, x_172);
lean_ctor_set(x_180, 2, x_173);
lean_ctor_set(x_180, 3, x_174);
lean_ctor_set(x_180, 4, x_175);
lean_ctor_set(x_180, 5, x_176);
lean_ctor_set(x_180, 6, x_177);
lean_ctor_set_uint64(x_180, sizeof(void*)*7, x_170);
lean_ctor_set_uint8(x_180, sizeof(void*)*7 + 8, x_171);
lean_ctor_set_uint8(x_180, sizeof(void*)*7 + 9, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*7 + 10, x_179);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_43);
lean_inc(x_99);
x_181 = l_Lean_Meta_isExprDefEq(x_99, x_43, x_180, x_13, x_14, x_15, x_97);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_101 = x_184;
x_102 = x_183;
goto block_142;
}
else
{
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_unbox(x_185);
lean_dec(x_185);
x_101 = x_187;
x_102 = x_186;
goto block_142;
}
else
{
uint8_t x_188; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_91);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_188 = !lean_is_exclusive(x_181);
if (x_188 == 0)
{
return x_181;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_181, 0);
x_190 = lean_ctor_get(x_181, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_181);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
block_142:
{
if (x_101 == 0)
{
lean_object* x_103; 
lean_dec(x_98);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_103 = l_Lean_Meta_addPPExplicitToExposeDiff(x_99, x_43, x_12, x_13, x_14, x_15, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_ctor_get(x_104, 1);
x_109 = lean_mk_string_unchecked("Term reduces to", 15, 15);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = l_Lean_indentExpr(x_107);
lean_ctor_set_tag(x_104, 7);
lean_ctor_set(x_104, 1, x_111);
lean_ctor_set(x_104, 0, x_110);
x_112 = lean_mk_string_unchecked("\nbut is expected to reduce to ", 30, 30);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
if (lean_is_scalar(x_100)) {
 x_114 = lean_alloc_ctor(7, 2, 0);
} else {
 x_114 = x_100;
 lean_ctor_set_tag(x_114, 7);
}
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_indentExpr(x_108);
if (lean_is_scalar(x_91)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_91;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked("", 0, 0);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
if (lean_is_scalar(x_75)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_75;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_119, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_121 = lean_ctor_get(x_104, 0);
x_122 = lean_ctor_get(x_104, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_104);
x_123 = lean_mk_string_unchecked("Term reduces to", 15, 15);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
x_125 = l_Lean_indentExpr(x_121);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_mk_string_unchecked("\nbut is expected to reduce to ", 30, 30);
x_128 = l_Lean_stringToMessageData(x_127);
lean_dec(x_127);
if (lean_is_scalar(x_100)) {
 x_129 = lean_alloc_ctor(7, 2, 0);
} else {
 x_129 = x_100;
 lean_ctor_set_tag(x_129, 7);
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_indentExpr(x_122);
if (lean_is_scalar(x_91)) {
 x_131 = lean_alloc_ctor(7, 2, 0);
} else {
 x_131 = x_91;
 lean_ctor_set_tag(x_131, 7);
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_mk_string_unchecked("", 0, 0);
x_133 = l_Lean_stringToMessageData(x_132);
lean_dec(x_132);
if (lean_is_scalar(x_75)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_75;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_134, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_100);
lean_dec(x_91);
lean_dec(x_75);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_136 = !lean_is_exclusive(x_103);
if (x_136 == 0)
{
return x_103;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_103, 0);
x_138 = lean_ctor_get(x_103, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_103);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_91);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_140 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_98;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_102);
return x_141;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_91);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_192 = !lean_is_exclusive(x_95);
if (x_192 == 0)
{
return x_95;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_95, 0);
x_194 = lean_ctor_get(x_95, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_95);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_91);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_196 = !lean_is_exclusive(x_92);
if (x_196 == 0)
{
return x_92;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_92, 0);
x_198 = lean_ctor_get(x_92, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_92);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_74);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_74, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_74, 0);
lean_dec(x_202);
x_203 = lean_ctor_get(x_72, 1);
lean_inc(x_203);
lean_dec(x_72);
x_204 = !lean_is_exclusive(x_88);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_205 = lean_ctor_get(x_88, 1);
lean_dec(x_205);
x_206 = lean_ctor_get(x_88, 0);
lean_dec(x_206);
x_207 = lean_mk_string_unchecked("", 0, 0);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = l_Lean_MessageData_ofSyntax(x_7);
lean_ctor_set_tag(x_88, 7);
lean_ctor_set(x_88, 1, x_209);
lean_ctor_set(x_88, 0, x_208);
x_210 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
x_211 = l_Lean_stringToMessageData(x_210);
lean_dec(x_210);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_211);
lean_ctor_set(x_74, 0, x_88);
x_212 = l_Lean_indentExpr(x_43);
if (lean_is_scalar(x_75)) {
 x_213 = lean_alloc_ctor(7, 2, 0);
} else {
 x_213 = x_75;
 lean_ctor_set_tag(x_213, 7);
}
lean_ctor_set(x_213, 0, x_74);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_mk_string_unchecked(".", 1, 1);
x_215 = l_Lean_stringToMessageData(x_214);
lean_dec(x_214);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_215);
lean_ctor_set(x_37, 0, x_213);
x_216 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_88);
x_217 = lean_mk_string_unchecked("", 0, 0);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
x_219 = l_Lean_MessageData_ofSyntax(x_7);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
x_222 = l_Lean_stringToMessageData(x_221);
lean_dec(x_221);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_222);
lean_ctor_set(x_74, 0, x_220);
x_223 = l_Lean_indentExpr(x_43);
if (lean_is_scalar(x_75)) {
 x_224 = lean_alloc_ctor(7, 2, 0);
} else {
 x_224 = x_75;
 lean_ctor_set_tag(x_224, 7);
}
lean_ctor_set(x_224, 0, x_74);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_mk_string_unchecked(".", 1, 1);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_226);
lean_ctor_set(x_37, 0, x_224);
x_227 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_74);
x_228 = lean_ctor_get(x_72, 1);
lean_inc(x_228);
lean_dec(x_72);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_229 = x_88;
} else {
 lean_dec_ref(x_88);
 x_229 = lean_box(0);
}
x_230 = lean_mk_string_unchecked("", 0, 0);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(7, 2, 0);
} else {
 x_233 = x_229;
 lean_ctor_set_tag(x_233, 7);
}
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
x_235 = l_Lean_stringToMessageData(x_234);
lean_dec(x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_indentExpr(x_43);
if (lean_is_scalar(x_75)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_75;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_mk_string_unchecked(".", 1, 1);
x_240 = l_Lean_stringToMessageData(x_239);
lean_dec(x_239);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_240);
lean_ctor_set(x_37, 0, x_238);
x_241 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_228);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_43);
lean_free_object(x_37);
lean_free_object(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_242 = !lean_is_exclusive(x_72);
if (x_242 == 0)
{
return x_72;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_72, 0);
x_244 = lean_ctor_get(x_72, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_72);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_free_object(x_37);
lean_dec(x_39);
lean_free_object(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_246 = !lean_is_exclusive(x_42);
if (x_246 == 0)
{
return x_42;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_42, 0);
x_248 = lean_ctor_get(x_42, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_42);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_37, 0);
x_251 = lean_ctor_get(x_37, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_37);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_27);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_253 = l_Lean_Elab_Term_elabTerm(x_3, x_252, x_2, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; size_t x_262; lean_object* x_263; lean_object* x_264; size_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Lean_Expr_mvarId_x21(x_250);
lean_dec(x_250);
x_257 = lean_box(0);
x_258 = lean_box(0);
x_259 = lean_box(0);
x_260 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_260, 0, x_259);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_usize_of_nat(x_4);
x_263 = lean_usize_to_nat(x_262);
x_264 = lean_nat_pow(x_261, x_263);
lean_dec(x_263);
x_265 = lean_usize_of_nat(x_264);
lean_dec(x_264);
x_266 = lean_usize_to_nat(x_265);
x_267 = lean_mk_empty_array_with_capacity(x_266);
lean_dec(x_266);
lean_inc(x_267);
x_268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_268, 0, x_267);
lean_inc(x_5);
x_269 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
lean_ctor_set(x_269, 2, x_5);
lean_ctor_set(x_269, 3, x_5);
lean_ctor_set_usize(x_269, 4, x_262);
x_270 = lean_box(0);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_272, 0, x_257);
lean_ctor_set(x_272, 1, x_258);
lean_ctor_set(x_272, 2, x_269);
lean_ctor_set(x_272, 3, x_260);
lean_ctor_set(x_272, 4, x_270);
lean_ctor_set(x_272, 5, x_270);
lean_ctor_set(x_272, 6, x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 1, x_2);
x_273 = lean_unbox(x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 2, x_273);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 4, x_2);
x_274 = lean_unbox(x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 5, x_274);
x_275 = lean_unbox(x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 6, x_275);
x_276 = lean_unbox(x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 7, x_276);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 8, x_2);
x_277 = lean_unbox(x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 9, x_277);
lean_ctor_set_uint8(x_272, sizeof(void*)*7 + 10, x_2);
x_278 = lean_box(0);
x_279 = lean_box(0);
x_280 = lean_box(0);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_282, 0, x_6);
lean_ctor_set(x_282, 1, x_270);
lean_ctor_set(x_282, 2, x_278);
lean_ctor_set(x_282, 3, x_279);
lean_ctor_set(x_282, 4, x_280);
lean_ctor_set(x_282, 5, x_270);
lean_ctor_set(x_282, 6, x_281);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_283 = l_Lean_Elab_runTactic(x_256, x_7, x_272, x_282, x_12, x_13, x_14, x_15, x_255);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_mk_string_unchecked("", 0, 0);
x_289 = l_Lean_stringToMessageData(x_288);
lean_dec(x_288);
x_290 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_286)) {
 x_291 = lean_alloc_ctor(7, 2, 0);
} else {
 x_291 = x_286;
 lean_ctor_set_tag(x_291, 7);
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_mk_string_unchecked(" closed goal, but is expected to reduce to ", 43, 43);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_indentExpr(x_254);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_295);
lean_ctor_set(x_29, 0, x_294);
x_296 = lean_mk_string_unchecked(".", 1, 1);
x_297 = l_Lean_stringToMessageData(x_296);
lean_dec(x_296);
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_29);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_298, x_10, x_11, x_12, x_13, x_14, x_15, x_287);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_299;
}
else
{
lean_object* x_300; 
lean_free_object(x_29);
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_7);
x_301 = lean_ctor_get(x_283, 1);
lean_inc(x_301);
lean_dec(x_283);
x_302 = lean_ctor_get(x_285, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_303 = x_285;
} else {
 lean_dec_ref(x_285);
 x_303 = lean_box(0);
}
x_304 = l_Lean_MVarId_getType(x_302, x_12, x_13, x_14, x_15, x_301);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_307 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_8, x_305, x_12, x_13, x_14, x_15, x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_341; lean_object* x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; uint8_t x_354; uint8_t x_355; uint8_t x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; uint64_t x_362; uint64_t x_363; uint64_t x_364; uint64_t x_365; uint8_t x_366; uint64_t x_367; uint64_t x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_310 = x_307;
} else {
 lean_dec_ref(x_307);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_308, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_312 = x_308;
} else {
 lean_dec_ref(x_308);
 x_312 = lean_box(0);
}
x_341 = lean_box(2);
x_342 = lean_ctor_get(x_12, 0);
lean_inc(x_342);
x_343 = lean_ctor_get_uint8(x_342, 0);
x_344 = lean_ctor_get_uint8(x_342, 1);
x_345 = lean_ctor_get_uint8(x_342, 2);
x_346 = lean_ctor_get_uint8(x_342, 3);
x_347 = lean_ctor_get_uint8(x_342, 4);
x_348 = lean_ctor_get_uint8(x_342, 5);
x_349 = lean_ctor_get_uint8(x_342, 6);
x_350 = lean_ctor_get_uint8(x_342, 7);
x_351 = lean_ctor_get_uint8(x_342, 8);
x_352 = lean_ctor_get_uint8(x_342, 10);
x_353 = lean_ctor_get_uint8(x_342, 11);
x_354 = lean_ctor_get_uint8(x_342, 12);
x_355 = lean_ctor_get_uint8(x_342, 13);
x_356 = lean_ctor_get_uint8(x_342, 14);
x_357 = lean_ctor_get_uint8(x_342, 15);
x_358 = lean_ctor_get_uint8(x_342, 16);
x_359 = lean_ctor_get_uint8(x_342, 17);
lean_dec(x_342);
x_360 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_360, 0, x_343);
lean_ctor_set_uint8(x_360, 1, x_344);
lean_ctor_set_uint8(x_360, 2, x_345);
lean_ctor_set_uint8(x_360, 3, x_346);
lean_ctor_set_uint8(x_360, 4, x_347);
lean_ctor_set_uint8(x_360, 5, x_348);
lean_ctor_set_uint8(x_360, 6, x_349);
lean_ctor_set_uint8(x_360, 7, x_350);
lean_ctor_set_uint8(x_360, 8, x_351);
x_361 = lean_unbox(x_341);
lean_ctor_set_uint8(x_360, 9, x_361);
lean_ctor_set_uint8(x_360, 10, x_352);
lean_ctor_set_uint8(x_360, 11, x_353);
lean_ctor_set_uint8(x_360, 12, x_354);
lean_ctor_set_uint8(x_360, 13, x_355);
lean_ctor_set_uint8(x_360, 14, x_356);
lean_ctor_set_uint8(x_360, 15, x_357);
lean_ctor_set_uint8(x_360, 16, x_358);
lean_ctor_set_uint8(x_360, 17, x_359);
x_362 = lean_ctor_get_uint64(x_12, sizeof(void*)*7);
x_363 = lean_uint64_of_nat(x_261);
x_364 = lean_uint64_shift_right(x_362, x_363);
x_365 = lean_uint64_shift_left(x_364, x_363);
x_366 = lean_unbox(x_341);
x_367 = l_Lean_Meta_TransparencyMode_toUInt64(x_366);
x_368 = lean_uint64_lor(x_365, x_367);
x_369 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 8);
x_370 = lean_ctor_get(x_12, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_12, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_12, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_12, 4);
lean_inc(x_373);
x_374 = lean_ctor_get(x_12, 5);
lean_inc(x_374);
x_375 = lean_ctor_get(x_12, 6);
lean_inc(x_375);
x_376 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 9);
x_377 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 10);
x_378 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_378, 0, x_360);
lean_ctor_set(x_378, 1, x_370);
lean_ctor_set(x_378, 2, x_371);
lean_ctor_set(x_378, 3, x_372);
lean_ctor_set(x_378, 4, x_373);
lean_ctor_set(x_378, 5, x_374);
lean_ctor_set(x_378, 6, x_375);
lean_ctor_set_uint64(x_378, sizeof(void*)*7, x_368);
lean_ctor_set_uint8(x_378, sizeof(void*)*7 + 8, x_369);
lean_ctor_set_uint8(x_378, sizeof(void*)*7 + 9, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*7 + 10, x_377);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_254);
lean_inc(x_311);
x_379 = l_Lean_Meta_isExprDefEq(x_311, x_254, x_378, x_13, x_14, x_15, x_309);
lean_dec(x_378);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_unbox(x_380);
lean_dec(x_380);
x_313 = x_382;
x_314 = x_381;
goto block_340;
}
else
{
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_383 = lean_ctor_get(x_379, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_379, 1);
lean_inc(x_384);
lean_dec(x_379);
x_385 = lean_unbox(x_383);
lean_dec(x_383);
x_313 = x_385;
x_314 = x_384;
goto block_340;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_303);
lean_dec(x_286);
lean_dec(x_254);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_386 = lean_ctor_get(x_379, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_379, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_388 = x_379;
} else {
 lean_dec_ref(x_379);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
block_340:
{
if (x_313 == 0)
{
lean_object* x_315; 
lean_dec(x_310);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_315 = l_Lean_Meta_addPPExplicitToExposeDiff(x_311, x_254, x_12, x_13, x_14, x_15, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_320 = x_316;
} else {
 lean_dec_ref(x_316);
 x_320 = lean_box(0);
}
x_321 = lean_mk_string_unchecked("Term reduces to", 15, 15);
x_322 = l_Lean_stringToMessageData(x_321);
lean_dec(x_321);
x_323 = l_Lean_indentExpr(x_318);
if (lean_is_scalar(x_320)) {
 x_324 = lean_alloc_ctor(7, 2, 0);
} else {
 x_324 = x_320;
 lean_ctor_set_tag(x_324, 7);
}
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_mk_string_unchecked("\nbut is expected to reduce to ", 30, 30);
x_326 = l_Lean_stringToMessageData(x_325);
lean_dec(x_325);
if (lean_is_scalar(x_312)) {
 x_327 = lean_alloc_ctor(7, 2, 0);
} else {
 x_327 = x_312;
 lean_ctor_set_tag(x_327, 7);
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_indentExpr(x_319);
if (lean_is_scalar(x_303)) {
 x_329 = lean_alloc_ctor(7, 2, 0);
} else {
 x_329 = x_303;
 lean_ctor_set_tag(x_329, 7);
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_mk_string_unchecked("", 0, 0);
x_331 = l_Lean_stringToMessageData(x_330);
lean_dec(x_330);
if (lean_is_scalar(x_286)) {
 x_332 = lean_alloc_ctor(7, 2, 0);
} else {
 x_332 = x_286;
 lean_ctor_set_tag(x_332, 7);
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_332, x_10, x_11, x_12, x_13, x_14, x_15, x_317);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_312);
lean_dec(x_303);
lean_dec(x_286);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_334 = lean_ctor_get(x_315, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_315, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_336 = x_315;
} else {
 lean_dec_ref(x_315);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_303);
lean_dec(x_286);
lean_dec(x_254);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_338 = lean_box(0);
if (lean_is_scalar(x_310)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_310;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_314);
return x_339;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_303);
lean_dec(x_286);
lean_dec(x_254);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_390 = lean_ctor_get(x_307, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_307, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_392 = x_307;
} else {
 lean_dec_ref(x_307);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_303);
lean_dec(x_286);
lean_dec(x_254);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_394 = lean_ctor_get(x_304, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_304, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_396 = x_304;
} else {
 lean_dec_ref(x_304);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_398 = x_285;
} else {
 lean_dec_ref(x_285);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_283, 1);
lean_inc(x_399);
lean_dec(x_283);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_400 = x_300;
} else {
 lean_dec_ref(x_300);
 x_400 = lean_box(0);
}
x_401 = lean_mk_string_unchecked("", 0, 0);
x_402 = l_Lean_stringToMessageData(x_401);
lean_dec(x_401);
x_403 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_400)) {
 x_404 = lean_alloc_ctor(7, 2, 0);
} else {
 x_404 = x_400;
 lean_ctor_set_tag(x_404, 7);
}
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
x_406 = l_Lean_stringToMessageData(x_405);
lean_dec(x_405);
if (lean_is_scalar(x_398)) {
 x_407 = lean_alloc_ctor(7, 2, 0);
} else {
 x_407 = x_398;
 lean_ctor_set_tag(x_407, 7);
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_indentExpr(x_254);
if (lean_is_scalar(x_286)) {
 x_409 = lean_alloc_ctor(7, 2, 0);
} else {
 x_409 = x_286;
 lean_ctor_set_tag(x_409, 7);
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_mk_string_unchecked(".", 1, 1);
x_411 = l_Lean_stringToMessageData(x_410);
lean_dec(x_410);
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_399);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_413;
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_254);
lean_free_object(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_414 = lean_ctor_get(x_283, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_283, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_416 = x_283;
} else {
 lean_dec_ref(x_283);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_250);
lean_free_object(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_418 = lean_ctor_get(x_253, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_253, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_420 = x_253;
} else {
 lean_dec_ref(x_253);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_422 = lean_ctor_get(x_29, 0);
x_423 = lean_ctor_get(x_29, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_29);
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_422);
x_425 = lean_box(0);
x_426 = lean_box(0);
x_427 = lean_unbox(x_425);
lean_inc(x_12);
x_428 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_424, x_427, x_426, x_12, x_13, x_14, x_15, x_423);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_27);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_433 = l_Lean_Elab_Term_elabTerm(x_3, x_432, x_2, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_430);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; size_t x_442; lean_object* x_443; lean_object* x_444; size_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = l_Lean_Expr_mvarId_x21(x_429);
lean_dec(x_429);
x_437 = lean_box(0);
x_438 = lean_box(0);
x_439 = lean_box(0);
x_440 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_440, 0, x_439);
x_441 = lean_unsigned_to_nat(2u);
x_442 = lean_usize_of_nat(x_4);
x_443 = lean_usize_to_nat(x_442);
x_444 = lean_nat_pow(x_441, x_443);
lean_dec(x_443);
x_445 = lean_usize_of_nat(x_444);
lean_dec(x_444);
x_446 = lean_usize_to_nat(x_445);
x_447 = lean_mk_empty_array_with_capacity(x_446);
lean_dec(x_446);
lean_inc(x_447);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_447);
lean_inc(x_5);
x_449 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
lean_ctor_set(x_449, 2, x_5);
lean_ctor_set(x_449, 3, x_5);
lean_ctor_set_usize(x_449, 4, x_442);
x_450 = lean_box(0);
x_451 = lean_box(0);
x_452 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_452, 0, x_437);
lean_ctor_set(x_452, 1, x_438);
lean_ctor_set(x_452, 2, x_449);
lean_ctor_set(x_452, 3, x_440);
lean_ctor_set(x_452, 4, x_450);
lean_ctor_set(x_452, 5, x_450);
lean_ctor_set(x_452, 6, x_451);
lean_ctor_set_uint8(x_452, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 1, x_2);
x_453 = lean_unbox(x_439);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 2, x_453);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 4, x_2);
x_454 = lean_unbox(x_439);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 5, x_454);
x_455 = lean_unbox(x_439);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 6, x_455);
x_456 = lean_unbox(x_439);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 7, x_456);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 8, x_2);
x_457 = lean_unbox(x_439);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 9, x_457);
lean_ctor_set_uint8(x_452, sizeof(void*)*7 + 10, x_2);
x_458 = lean_box(0);
x_459 = lean_box(0);
x_460 = lean_box(0);
x_461 = lean_box(0);
x_462 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_462, 0, x_6);
lean_ctor_set(x_462, 1, x_450);
lean_ctor_set(x_462, 2, x_458);
lean_ctor_set(x_462, 3, x_459);
lean_ctor_set(x_462, 4, x_460);
lean_ctor_set(x_462, 5, x_450);
lean_ctor_set(x_462, 6, x_461);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_463 = l_Lean_Elab_runTactic(x_436, x_7, x_452, x_462, x_12, x_13, x_14, x_15, x_435);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_467 = lean_ctor_get(x_463, 1);
lean_inc(x_467);
lean_dec(x_463);
x_468 = lean_mk_string_unchecked("", 0, 0);
x_469 = l_Lean_stringToMessageData(x_468);
lean_dec(x_468);
x_470 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(7, 2, 0);
} else {
 x_471 = x_466;
 lean_ctor_set_tag(x_471, 7);
}
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_mk_string_unchecked(" closed goal, but is expected to reduce to ", 43, 43);
x_473 = l_Lean_stringToMessageData(x_472);
lean_dec(x_472);
if (lean_is_scalar(x_431)) {
 x_474 = lean_alloc_ctor(7, 2, 0);
} else {
 x_474 = x_431;
 lean_ctor_set_tag(x_474, 7);
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_473);
x_475 = l_Lean_indentExpr(x_434);
x_476 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
x_477 = lean_mk_string_unchecked(".", 1, 1);
x_478 = l_Lean_stringToMessageData(x_477);
lean_dec(x_477);
x_479 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_479, x_10, x_11, x_12, x_13, x_14, x_15, x_467);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_480;
}
else
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_465, 1);
lean_inc(x_481);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_431);
lean_dec(x_7);
x_482 = lean_ctor_get(x_463, 1);
lean_inc(x_482);
lean_dec(x_463);
x_483 = lean_ctor_get(x_465, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_484 = x_465;
} else {
 lean_dec_ref(x_465);
 x_484 = lean_box(0);
}
x_485 = l_Lean_MVarId_getType(x_483, x_12, x_13, x_14, x_15, x_482);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_488 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_8, x_486, x_12, x_13, x_14, x_15, x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_522; lean_object* x_523; uint8_t x_524; uint8_t x_525; uint8_t x_526; uint8_t x_527; uint8_t x_528; uint8_t x_529; uint8_t x_530; uint8_t x_531; uint8_t x_532; uint8_t x_533; uint8_t x_534; uint8_t x_535; uint8_t x_536; uint8_t x_537; uint8_t x_538; uint8_t x_539; uint8_t x_540; lean_object* x_541; uint8_t x_542; uint64_t x_543; uint64_t x_544; uint64_t x_545; uint64_t x_546; uint8_t x_547; uint64_t x_548; uint64_t x_549; uint8_t x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; uint8_t x_558; lean_object* x_559; lean_object* x_560; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_489, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_493 = x_489;
} else {
 lean_dec_ref(x_489);
 x_493 = lean_box(0);
}
x_522 = lean_box(2);
x_523 = lean_ctor_get(x_12, 0);
lean_inc(x_523);
x_524 = lean_ctor_get_uint8(x_523, 0);
x_525 = lean_ctor_get_uint8(x_523, 1);
x_526 = lean_ctor_get_uint8(x_523, 2);
x_527 = lean_ctor_get_uint8(x_523, 3);
x_528 = lean_ctor_get_uint8(x_523, 4);
x_529 = lean_ctor_get_uint8(x_523, 5);
x_530 = lean_ctor_get_uint8(x_523, 6);
x_531 = lean_ctor_get_uint8(x_523, 7);
x_532 = lean_ctor_get_uint8(x_523, 8);
x_533 = lean_ctor_get_uint8(x_523, 10);
x_534 = lean_ctor_get_uint8(x_523, 11);
x_535 = lean_ctor_get_uint8(x_523, 12);
x_536 = lean_ctor_get_uint8(x_523, 13);
x_537 = lean_ctor_get_uint8(x_523, 14);
x_538 = lean_ctor_get_uint8(x_523, 15);
x_539 = lean_ctor_get_uint8(x_523, 16);
x_540 = lean_ctor_get_uint8(x_523, 17);
lean_dec(x_523);
x_541 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_541, 0, x_524);
lean_ctor_set_uint8(x_541, 1, x_525);
lean_ctor_set_uint8(x_541, 2, x_526);
lean_ctor_set_uint8(x_541, 3, x_527);
lean_ctor_set_uint8(x_541, 4, x_528);
lean_ctor_set_uint8(x_541, 5, x_529);
lean_ctor_set_uint8(x_541, 6, x_530);
lean_ctor_set_uint8(x_541, 7, x_531);
lean_ctor_set_uint8(x_541, 8, x_532);
x_542 = lean_unbox(x_522);
lean_ctor_set_uint8(x_541, 9, x_542);
lean_ctor_set_uint8(x_541, 10, x_533);
lean_ctor_set_uint8(x_541, 11, x_534);
lean_ctor_set_uint8(x_541, 12, x_535);
lean_ctor_set_uint8(x_541, 13, x_536);
lean_ctor_set_uint8(x_541, 14, x_537);
lean_ctor_set_uint8(x_541, 15, x_538);
lean_ctor_set_uint8(x_541, 16, x_539);
lean_ctor_set_uint8(x_541, 17, x_540);
x_543 = lean_ctor_get_uint64(x_12, sizeof(void*)*7);
x_544 = lean_uint64_of_nat(x_441);
x_545 = lean_uint64_shift_right(x_543, x_544);
x_546 = lean_uint64_shift_left(x_545, x_544);
x_547 = lean_unbox(x_522);
x_548 = l_Lean_Meta_TransparencyMode_toUInt64(x_547);
x_549 = lean_uint64_lor(x_546, x_548);
x_550 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 8);
x_551 = lean_ctor_get(x_12, 1);
lean_inc(x_551);
x_552 = lean_ctor_get(x_12, 2);
lean_inc(x_552);
x_553 = lean_ctor_get(x_12, 3);
lean_inc(x_553);
x_554 = lean_ctor_get(x_12, 4);
lean_inc(x_554);
x_555 = lean_ctor_get(x_12, 5);
lean_inc(x_555);
x_556 = lean_ctor_get(x_12, 6);
lean_inc(x_556);
x_557 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 9);
x_558 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 10);
x_559 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_559, 0, x_541);
lean_ctor_set(x_559, 1, x_551);
lean_ctor_set(x_559, 2, x_552);
lean_ctor_set(x_559, 3, x_553);
lean_ctor_set(x_559, 4, x_554);
lean_ctor_set(x_559, 5, x_555);
lean_ctor_set(x_559, 6, x_556);
lean_ctor_set_uint64(x_559, sizeof(void*)*7, x_549);
lean_ctor_set_uint8(x_559, sizeof(void*)*7 + 8, x_550);
lean_ctor_set_uint8(x_559, sizeof(void*)*7 + 9, x_557);
lean_ctor_set_uint8(x_559, sizeof(void*)*7 + 10, x_558);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_434);
lean_inc(x_492);
x_560 = l_Lean_Meta_isExprDefEq(x_492, x_434, x_559, x_13, x_14, x_15, x_490);
lean_dec(x_559);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = lean_unbox(x_561);
lean_dec(x_561);
x_494 = x_563;
x_495 = x_562;
goto block_521;
}
else
{
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_564 = lean_ctor_get(x_560, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_560, 1);
lean_inc(x_565);
lean_dec(x_560);
x_566 = lean_unbox(x_564);
lean_dec(x_564);
x_494 = x_566;
x_495 = x_565;
goto block_521;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_484);
lean_dec(x_466);
lean_dec(x_434);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_567 = lean_ctor_get(x_560, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_560, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_569 = x_560;
} else {
 lean_dec_ref(x_560);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
block_521:
{
if (x_494 == 0)
{
lean_object* x_496; 
lean_dec(x_491);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_496 = l_Lean_Meta_addPPExplicitToExposeDiff(x_492, x_434, x_12, x_13, x_14, x_15, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_501 = x_497;
} else {
 lean_dec_ref(x_497);
 x_501 = lean_box(0);
}
x_502 = lean_mk_string_unchecked("Term reduces to", 15, 15);
x_503 = l_Lean_stringToMessageData(x_502);
lean_dec(x_502);
x_504 = l_Lean_indentExpr(x_499);
if (lean_is_scalar(x_501)) {
 x_505 = lean_alloc_ctor(7, 2, 0);
} else {
 x_505 = x_501;
 lean_ctor_set_tag(x_505, 7);
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_mk_string_unchecked("\nbut is expected to reduce to ", 30, 30);
x_507 = l_Lean_stringToMessageData(x_506);
lean_dec(x_506);
if (lean_is_scalar(x_493)) {
 x_508 = lean_alloc_ctor(7, 2, 0);
} else {
 x_508 = x_493;
 lean_ctor_set_tag(x_508, 7);
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_507);
x_509 = l_Lean_indentExpr(x_500);
if (lean_is_scalar(x_484)) {
 x_510 = lean_alloc_ctor(7, 2, 0);
} else {
 x_510 = x_484;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
x_511 = lean_mk_string_unchecked("", 0, 0);
x_512 = l_Lean_stringToMessageData(x_511);
lean_dec(x_511);
if (lean_is_scalar(x_466)) {
 x_513 = lean_alloc_ctor(7, 2, 0);
} else {
 x_513 = x_466;
 lean_ctor_set_tag(x_513, 7);
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_512);
x_514 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_513, x_10, x_11, x_12, x_13, x_14, x_15, x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_493);
lean_dec(x_484);
lean_dec(x_466);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_515 = lean_ctor_get(x_496, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_496, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_517 = x_496;
} else {
 lean_dec_ref(x_496);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
else
{
lean_object* x_519; lean_object* x_520; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_484);
lean_dec(x_466);
lean_dec(x_434);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_519 = lean_box(0);
if (lean_is_scalar(x_491)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_491;
}
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_495);
return x_520;
}
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_484);
lean_dec(x_466);
lean_dec(x_434);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_571 = lean_ctor_get(x_488, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_488, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_573 = x_488;
} else {
 lean_dec_ref(x_488);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_572);
return x_574;
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_484);
lean_dec(x_466);
lean_dec(x_434);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_575 = lean_ctor_get(x_485, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_485, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_577 = x_485;
} else {
 lean_dec_ref(x_485);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_579 = x_465;
} else {
 lean_dec_ref(x_465);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_463, 1);
lean_inc(x_580);
lean_dec(x_463);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_581 = x_481;
} else {
 lean_dec_ref(x_481);
 x_581 = lean_box(0);
}
x_582 = lean_mk_string_unchecked("", 0, 0);
x_583 = l_Lean_stringToMessageData(x_582);
lean_dec(x_582);
x_584 = l_Lean_MessageData_ofSyntax(x_7);
if (lean_is_scalar(x_581)) {
 x_585 = lean_alloc_ctor(7, 2, 0);
} else {
 x_585 = x_581;
 lean_ctor_set_tag(x_585, 7);
}
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
x_587 = l_Lean_stringToMessageData(x_586);
lean_dec(x_586);
if (lean_is_scalar(x_579)) {
 x_588 = lean_alloc_ctor(7, 2, 0);
} else {
 x_588 = x_579;
 lean_ctor_set_tag(x_588, 7);
}
lean_ctor_set(x_588, 0, x_585);
lean_ctor_set(x_588, 1, x_587);
x_589 = l_Lean_indentExpr(x_434);
if (lean_is_scalar(x_466)) {
 x_590 = lean_alloc_ctor(7, 2, 0);
} else {
 x_590 = x_466;
 lean_ctor_set_tag(x_590, 7);
}
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_mk_string_unchecked(".", 1, 1);
x_592 = l_Lean_stringToMessageData(x_591);
lean_dec(x_591);
if (lean_is_scalar(x_431)) {
 x_593 = lean_alloc_ctor(7, 2, 0);
} else {
 x_593 = x_431;
 lean_ctor_set_tag(x_593, 7);
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_592);
x_594 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_8, x_593, x_10, x_11, x_12, x_13, x_14, x_15, x_580);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_594;
}
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_434);
lean_dec(x_431);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_595 = lean_ctor_get(x_463, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_463, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_597 = x_463;
} else {
 lean_dec_ref(x_463);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_596);
return x_598;
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_599 = lean_ctor_get(x_433, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_433, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_601 = x_433;
} else {
 lean_dec_ref(x_433);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_600);
return x_602;
}
}
}
else
{
uint8_t x_603; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_603 = !lean_is_exclusive(x_26);
if (x_603 == 0)
{
return x_26;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_26, 0);
x_605 = lean_ctor_get(x_26, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_26);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
else
{
uint8_t x_607; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_607 = !lean_is_exclusive(x_23);
if (x_607 == 0)
{
return x_23;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_608 = lean_ctor_get(x_23, 0);
x_609 = lean_ctor_get(x_23, 1);
lean_inc(x_609);
lean_inc(x_608);
lean_dec(x_23);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set(x_610, 1, x_609);
return x_610;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("checkTactic", 11, 11);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_st_ref_get(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_1, x_11);
x_18 = l_Lean_Syntax_getArg(x_1, x_12);
x_19 = lean_unsigned_to_nat(5u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_box(0);
x_22 = lean_box(x_9);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 16, 8);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_18);
lean_closure_set(x_23, 3, x_19);
lean_closure_set(x_23, 4, x_16);
lean_closure_set(x_23, 5, x_21);
lean_closure_set(x_23, 6, x_20);
lean_closure_set(x_23, 7, x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lean_Environment_unlockAsync(x_25);
lean_dec(x_25);
x_27 = l_Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0(lean_box(0), x_26, x_24, x_2, x_3, x_15);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("checkTactic", 11, 11);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_9 = lean_mk_string_unchecked("elabCheckTactic", 15, 15);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_5 = lean_mk_string_unchecked("elabCheckTactic", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(24u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(45u);
x_11 = lean_unsigned_to_nat(95u);
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
x_16 = lean_unsigned_to_nat(19u);
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
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_MVarId_getType(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_14, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_indentExpr(x_21);
lean_inc(x_27);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_18);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_3;
x_3 = x_12;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
x_30 = lean_mk_string_unchecked("", 0, 0);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_indentExpr(x_21);
lean_inc(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_31);
lean_ctor_set(x_17, 0, x_33);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_3;
x_3 = x_12;
x_8 = x_19;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = l_Lean_indentExpr(x_35);
lean_inc(x_38);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(7, 2, 0);
} else {
 x_40 = x_36;
 lean_ctor_set_tag(x_40, 7);
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_3;
x_3 = x_12;
x_8 = x_19;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
x_53 = l_Lean_MVarId_getType(x_51, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_54, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_mk_string_unchecked("", 0, 0);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = l_Lean_indentExpr(x_60);
lean_inc(x_64);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(7, 2, 0);
} else {
 x_66 = x_62;
 lean_ctor_set_tag(x_66, 7);
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(7, 2, 0);
} else {
 x_67 = x_61;
 lean_ctor_set_tag(x_67, 7);
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_67);
x_2 = x_68;
x_3 = x_52;
x_8 = x_59;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_74 = lean_ctor_get(x_53, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_76 = x_53;
} else {
 lean_dec_ref(x_53);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = l_Lean_MVarId_getType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_indentExpr(x_23);
lean_inc(x_29);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_30);
lean_ctor_set(x_20, 0, x_29);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_20);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_2);
x_31 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_3, x_14, x_6, x_7, x_8, x_9, x_21);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
x_32 = lean_mk_string_unchecked("", 0, 0);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_indentExpr(x_23);
lean_inc(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_35);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_2);
x_36 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_3, x_14, x_6, x_7, x_8, x_9, x_21);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_indentExpr(x_37);
lean_inc(x_40);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(7, 2, 0);
} else {
 x_42 = x_38;
 lean_ctor_set_tag(x_42, 7);
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_43);
lean_ctor_set(x_3, 0, x_2);
x_44 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_3, x_14, x_6, x_7, x_8, x_9, x_21);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_15, 0);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_15);
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
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_55 = l_Lean_MVarId_getType(x_53, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_58 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_56, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_indentExpr(x_62);
lean_inc(x_66);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(7, 2, 0);
} else {
 x_68 = x_64;
 lean_ctor_set_tag(x_68, 7);
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_63;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_70, x_54, x_6, x_7, x_8, x_9, x_61);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_74 = x_58;
} else {
 lean_dec_ref(x_58);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_55, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_78 = x_55;
} else {
 lean_dec_ref(x_55);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_runTactic(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
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
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_19; lean_object* x_271; lean_object* x_272; 
x_271 = lean_box(0);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_272 = l_Lean_Elab_Term_elabTerm(x_1, x_271, x_2, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_273);
x_275 = lean_infer_type(x_273, x_10, x_11, x_12, x_13, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; size_t x_295; lean_object* x_296; lean_object* x_297; size_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_273, x_276, x_10, x_11, x_12, x_13, x_277);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_279);
x_282 = lean_box(0);
x_283 = lean_box(0);
x_284 = lean_unbox(x_282);
lean_inc(x_10);
x_285 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_281, x_284, x_283, x_10, x_11, x_12, x_13, x_280);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Expr_mvarId_x21(x_286);
lean_dec(x_286);
x_289 = lean_box(0);
x_290 = lean_box(0);
x_291 = lean_box(0);
x_292 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_292, 0, x_291);
x_293 = lean_unsigned_to_nat(2u);
x_294 = lean_unsigned_to_nat(5u);
x_295 = lean_usize_of_nat(x_294);
x_296 = lean_usize_to_nat(x_295);
x_297 = lean_nat_pow(x_293, x_296);
lean_dec(x_296);
x_298 = lean_usize_of_nat(x_297);
lean_dec(x_297);
x_299 = lean_usize_to_nat(x_298);
x_300 = lean_mk_empty_array_with_capacity(x_299);
lean_dec(x_299);
lean_inc(x_300);
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_300);
lean_inc(x_5);
x_302 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
lean_ctor_set(x_302, 2, x_5);
lean_ctor_set(x_302, 3, x_5);
lean_ctor_set_usize(x_302, 4, x_295);
x_303 = lean_box(0);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_305, 0, x_289);
lean_ctor_set(x_305, 1, x_290);
lean_ctor_set(x_305, 2, x_302);
lean_ctor_set(x_305, 3, x_292);
lean_ctor_set(x_305, 4, x_303);
lean_ctor_set(x_305, 5, x_303);
lean_ctor_set(x_305, 6, x_304);
lean_ctor_set_uint8(x_305, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 1, x_2);
x_306 = lean_unbox(x_291);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 2, x_306);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 4, x_2);
x_307 = lean_unbox(x_291);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 5, x_307);
x_308 = lean_unbox(x_291);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 6, x_308);
x_309 = lean_unbox(x_291);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 7, x_309);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 8, x_2);
x_310 = lean_unbox(x_291);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 9, x_310);
lean_ctor_set_uint8(x_305, sizeof(void*)*7 + 10, x_2);
x_311 = lean_box(0);
x_312 = lean_box(0);
x_313 = lean_box(0);
x_314 = lean_box(0);
x_315 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_315, 0, x_6);
lean_ctor_set(x_315, 1, x_303);
lean_ctor_set(x_315, 2, x_311);
lean_ctor_set(x_315, 3, x_312);
lean_ctor_set(x_315, 4, x_313);
lean_ctor_set(x_315, 5, x_303);
lean_ctor_set(x_315, 6, x_314);
lean_inc(x_3);
x_316 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(x_316, 0, x_288);
lean_closure_set(x_316, 1, x_3);
lean_closure_set(x_316, 2, x_305);
lean_closure_set(x_316, 3, x_315);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_317 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_316, x_8, x_9, x_10, x_11, x_12, x_13, x_287);
if (lean_obj_tag(x_317) == 0)
{
x_19 = x_317;
goto block_270;
}
else
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_322; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
x_322 = l_Lean_Exception_isInterrupt(x_318);
if (x_322 == 0)
{
uint8_t x_323; 
x_323 = l_Lean_Exception_isRuntime(x_318);
lean_dec(x_318);
x_320 = x_323;
goto block_321;
}
else
{
lean_dec(x_318);
x_320 = x_322;
goto block_321;
}
block_321:
{
if (x_320 == 0)
{
lean_dec(x_317);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_15 = x_319;
goto block_18;
}
else
{
lean_dec(x_319);
x_19 = x_317;
goto block_270;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_273);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_275);
if (x_324 == 0)
{
return x_275;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_275, 0);
x_326 = lean_ctor_get(x_275, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_275);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_272);
if (x_328 == 0)
{
return x_272;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_272, 0);
x_330 = lean_ctor_get(x_272, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_272);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_270:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_15 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_3);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_29);
lean_ctor_set(x_22, 0, x_28);
x_30 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofSyntax(x_1);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(", but closed goal.", 18, 18);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_dec(x_43);
x_44 = l_Lean_MVarId_getType(x_42, x_10, x_11, x_12, x_13, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_47 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_45, x_10, x_11, x_12, x_13, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_49, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_49, 0);
lean_dec(x_56);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = l_Lean_indentExpr(x_52);
lean_inc(x_58);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_59);
lean_ctor_set(x_49, 0, x_58);
lean_inc(x_58);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_58);
lean_ctor_set(x_48, 0, x_49);
x_60 = l_Lean_MessageData_ofSyntax(x_3);
lean_inc(x_58);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_60);
lean_ctor_set(x_24, 0, x_58);
x_61 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_62);
x_63 = l_Lean_MessageData_ofSyntax(x_1);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_22);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked(", but returned: ", 16, 16);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_48);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_58);
x_70 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_49);
x_71 = lean_mk_string_unchecked("", 0, 0);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = l_Lean_indentExpr(x_52);
lean_inc(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_72);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_72);
lean_ctor_set(x_48, 0, x_74);
x_75 = l_Lean_MessageData_ofSyntax(x_3);
lean_inc(x_72);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_75);
lean_ctor_set(x_24, 0, x_72);
x_76 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_77);
x_78 = l_Lean_MessageData_ofSyntax(x_1);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_22);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked(", but returned: ", 16, 16);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_48);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_72);
x_85 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_86 = lean_ctor_get(x_48, 0);
lean_inc(x_86);
lean_dec(x_48);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_87 = x_49;
} else {
 lean_dec_ref(x_49);
 x_87 = lean_box(0);
}
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = l_Lean_indentExpr(x_86);
lean_inc(x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(7, 2, 0);
} else {
 x_91 = x_87;
 lean_ctor_set_tag(x_91, 7);
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_89);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
x_93 = l_Lean_MessageData_ofSyntax(x_3);
lean_inc(x_89);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_93);
lean_ctor_set(x_24, 0, x_89);
x_94 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_95);
x_96 = l_Lean_MessageData_ofSyntax(x_1);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_22);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked(", but returned: ", 16, 16);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_92);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_89);
x_103 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_free_object(x_24);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_47);
if (x_104 == 0)
{
return x_47;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_47, 0);
x_106 = lean_ctor_get(x_47, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_47);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_24);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_44);
if (x_108 == 0)
{
return x_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_44, 0);
x_110 = lean_ctor_get(x_44, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_44);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_24, 0);
lean_inc(x_112);
lean_dec(x_24);
x_113 = l_Lean_MVarId_getType(x_112, x_10, x_11, x_12, x_13, x_40);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_116 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_114, x_10, x_11, x_12, x_13, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_mk_string_unchecked("", 0, 0);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
x_125 = l_Lean_indentExpr(x_120);
lean_inc(x_124);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_122;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_124);
if (lean_is_scalar(x_121)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_121;
 lean_ctor_set_tag(x_127, 7);
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = l_Lean_MessageData_ofSyntax(x_3);
lean_inc(x_124);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_131);
lean_ctor_set(x_22, 0, x_129);
x_132 = l_Lean_MessageData_ofSyntax(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_22);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked(", but returned: ", 16, 16);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_127);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_124);
x_139 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_138, x_8, x_9, x_10, x_11, x_12, x_13, x_119);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_ctor_get(x_116, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_116, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_142 = x_116;
} else {
 lean_dec_ref(x_116);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_ctor_get(x_113, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_113, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_146 = x_113;
} else {
 lean_dec_ref(x_113);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_19, 1);
lean_inc(x_148);
lean_dec(x_19);
x_149 = !lean_is_exclusive(x_39);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_150 = lean_ctor_get(x_39, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_39, 0);
lean_dec(x_151);
x_152 = lean_mk_string_unchecked("", 0, 0);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = l_Lean_MessageData_ofSyntax(x_3);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_154);
lean_ctor_set(x_39, 0, x_153);
x_155 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_156 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_156);
lean_ctor_set(x_22, 0, x_39);
x_157 = l_Lean_MessageData_ofSyntax(x_1);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_22);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked(", but returned goals:", 21, 21);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_162 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_161, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_148);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_163, x_8, x_9, x_10, x_11, x_12, x_13, x_164);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_165;
}
else
{
uint8_t x_166; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
return x_162;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_162, 0);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_162);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_39);
x_170 = lean_mk_string_unchecked("", 0, 0);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
x_172 = l_Lean_MessageData_ofSyntax(x_3);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_175);
lean_ctor_set(x_22, 0, x_173);
x_176 = l_Lean_MessageData_ofSyntax(x_1);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_22);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_mk_string_unchecked(", but returned goals:", 21, 21);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_181 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_180, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_148);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_182, x_8, x_9, x_10, x_11, x_12, x_13, x_183);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
else
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_22, 0);
lean_inc(x_189);
lean_dec(x_22);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_190 = lean_ctor_get(x_19, 1);
lean_inc(x_190);
lean_dec(x_19);
x_191 = lean_mk_string_unchecked("", 0, 0);
x_192 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
x_193 = l_Lean_MessageData_ofSyntax(x_3);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_196 = l_Lean_stringToMessageData(x_195);
lean_dec(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_MessageData_ofSyntax(x_1);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_mk_string_unchecked(", but closed goal.", 18, 18);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_202, x_8, x_9, x_10, x_11, x_12, x_13, x_190);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_203;
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_189, 1);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_19, 1);
lean_inc(x_205);
lean_dec(x_19);
x_206 = lean_ctor_get(x_189, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_207 = x_189;
} else {
 lean_dec_ref(x_189);
 x_207 = lean_box(0);
}
x_208 = l_Lean_MVarId_getType(x_206, x_10, x_11, x_12, x_13, x_205);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_211 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_209, x_10, x_11, x_12, x_13, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_216 = x_212;
} else {
 lean_dec_ref(x_212);
 x_216 = lean_box(0);
}
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_217 = x_213;
} else {
 lean_dec_ref(x_213);
 x_217 = lean_box(0);
}
x_218 = lean_mk_string_unchecked("", 0, 0);
x_219 = l_Lean_stringToMessageData(x_218);
lean_dec(x_218);
x_220 = l_Lean_indentExpr(x_215);
lean_inc(x_219);
if (lean_is_scalar(x_217)) {
 x_221 = lean_alloc_ctor(7, 2, 0);
} else {
 x_221 = x_217;
 lean_ctor_set_tag(x_221, 7);
}
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
lean_inc(x_219);
if (lean_is_scalar(x_216)) {
 x_222 = lean_alloc_ctor(7, 2, 0);
} else {
 x_222 = x_216;
 lean_ctor_set_tag(x_222, 7);
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
x_223 = l_Lean_MessageData_ofSyntax(x_3);
lean_inc(x_219);
if (lean_is_scalar(x_207)) {
 x_224 = lean_alloc_ctor(7, 2, 0);
} else {
 x_224 = x_207;
 lean_ctor_set_tag(x_224, 7);
}
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_MessageData_ofSyntax(x_1);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_mk_string_unchecked(", but returned: ", 16, 16);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_222);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_219);
x_235 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_234, x_8, x_9, x_10, x_11, x_12, x_13, x_214);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_207);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_236 = lean_ctor_get(x_211, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_211, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_238 = x_211;
} else {
 lean_dec_ref(x_211);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_207);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_208, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_242 = x_208;
} else {
 lean_dec_ref(x_208);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_244 = lean_ctor_get(x_19, 1);
lean_inc(x_244);
lean_dec(x_19);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_245 = x_204;
} else {
 lean_dec_ref(x_204);
 x_245 = lean_box(0);
}
x_246 = lean_mk_string_unchecked("", 0, 0);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
x_248 = l_Lean_MessageData_ofSyntax(x_3);
if (lean_is_scalar(x_245)) {
 x_249 = lean_alloc_ctor(7, 2, 0);
} else {
 x_249 = x_245;
 lean_ctor_set_tag(x_249, 7);
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_MessageData_ofSyntax(x_1);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_mk_string_unchecked(", but returned goals:", 21, 21);
x_256 = l_Lean_stringToMessageData(x_255);
lean_dec(x_255);
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_256);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_258 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_257, x_189, x_8, x_9, x_10, x_11, x_12, x_13, x_244);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_4, x_259, x_8, x_9, x_10, x_11, x_12, x_13, x_260);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_262 = lean_ctor_get(x_258, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_264 = x_258;
} else {
 lean_dec_ref(x_258);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_19);
if (x_266 == 0)
{
return x_19;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_19, 0);
x_268 = lean_ctor_get(x_19, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_19);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("checkTacticFailure", 18, 18);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_st_ref_get(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_1, x_11);
x_18 = l_Lean_Syntax_getArg(x_1, x_12);
x_19 = lean_box(0);
x_20 = lean_box(x_9);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_16);
lean_closure_set(x_21, 5, x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_21);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Environment_unlockAsync(x_23);
lean_dec(x_23);
x_25 = l_Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0(lean_box(0), x_24, x_22, x_2, x_3, x_15);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("checkTacticFailure", 18, 18);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_9 = lean_mk_string_unchecked("elabCheckTacticFailure", 22, 22);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_5 = lean_mk_string_unchecked("elabCheckTacticFailure", 22, 22);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(48u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(73u);
x_11 = lean_unsigned_to_nat(30u);
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
x_16 = lean_unsigned_to_nat(26u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("checkSimp", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
x_18 = lean_mk_string_unchecked("checkTactic", 11, 11);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Name_mkStr3(x_4, x_5, x_18);
x_20 = lean_mk_string_unchecked("#check_tactic", 13, 13);
lean_inc(x_17);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("~>", 2, 2);
lean_inc(x_17);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_17);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("Tactic", 6, 6);
x_27 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_26, x_27);
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_mk_string_unchecked("optConfig", 9, 9);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_26, x_30);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Array_mkArray0(lean_box(0));
lean_inc(x_17);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_35);
lean_inc(x_17);
x_36 = l_Lean_Syntax_node1(x_17, x_31, x_35);
lean_inc_n(x_35, 3);
lean_inc(x_17);
x_37 = l_Lean_Syntax_node6(x_17, x_28, x_29, x_36, x_35, x_35, x_35, x_35);
x_38 = l_Lean_Syntax_node6(x_17, x_19, x_21, x_11, x_23, x_13, x_25, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("checkSimp", 9, 9);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_9 = lean_mk_string_unchecked("expandCheckSimp", 15, 15);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_5 = lean_mk_string_unchecked("expandCheckSimp", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(76u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(78u);
x_11 = lean_unsigned_to_nat(45u);
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
x_16 = lean_unsigned_to_nat(19u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("checkSimpFailure", 16, 16);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("checkTacticFailure", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Name_mkStr3(x_4, x_5, x_16);
x_18 = lean_mk_string_unchecked("#check_tactic_failure", 21, 21);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("by", 2, 2);
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_23);
lean_inc(x_15);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked("optConfig", 9, 9);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_22, x_26);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Array_mkArray0(lean_box(0));
lean_inc(x_15);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_inc(x_31);
lean_inc(x_15);
x_32 = l_Lean_Syntax_node1(x_15, x_27, x_31);
lean_inc_n(x_31, 3);
lean_inc(x_15);
x_33 = l_Lean_Syntax_node6(x_15, x_24, x_25, x_32, x_31, x_31, x_31, x_31);
x_34 = l_Lean_Syntax_node4(x_15, x_17, x_19, x_11, x_21, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("checkSimpFailure", 16, 16);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_9 = lean_mk_string_unchecked("expandCheckSimpFailure", 22, 22);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_5 = lean_mk_string_unchecked("expandCheckSimpFailure", 22, 22);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(81u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(83u);
x_11 = lean_unsigned_to_nat(45u);
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
x_16 = lean_unsigned_to_nat(26u);
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
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_CheckTactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CheckTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
