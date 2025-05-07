// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
// Imports: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide Lean.Elab.Tactic.BVDecide.Frontend.BVCheck Lean.Elab.Tactic.BVDecide.LRAT.Trim Lean.Meta.Tactic.TryThis Std.Tactic.BVDecide.Syntax
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
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0___boxed(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l_System_FilePath_fileName(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_string_unchecked("could not find file name", 24, 24);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_1, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_mk_string_unchecked("could not find declaration name", 31, 31);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_getRefPos___at___Lean_getRefPosition___at___Lean_Elab_Term_elabPanic_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0___boxed), 1, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = l_Lean_FileMap_toPosition(x_26, x_24);
lean_dec(x_24);
x_28 = lean_mk_string_unchecked("-", 1, 1);
x_29 = lean_string_append(x_13, x_28);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Name_toString(x_21, x_31, x_25);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_28);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_35);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_28);
lean_dec(x_28);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_39);
x_41 = lean_string_append(x_38, x_40);
lean_dec(x_40);
x_42 = lean_mk_string_unchecked(".lrat", 5, 5);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
lean_ctor_set(x_22, 0, x_43);
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0___boxed), 1, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_dec(x_5);
x_48 = l_Lean_FileMap_toPosition(x_47, x_44);
lean_dec(x_44);
x_49 = lean_mk_string_unchecked("-", 1, 1);
x_50 = lean_string_append(x_13, x_49);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_21, x_52, x_46);
x_54 = lean_string_append(x_50, x_53);
lean_dec(x_53);
x_55 = lean_string_append(x_54, x_49);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = l___private_Init_Data_Repr_0__Nat_reprFast(x_56);
x_58 = lean_string_append(x_55, x_57);
lean_dec(x_57);
x_59 = lean_string_append(x_58, x_49);
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_61 = l___private_Init_Data_Repr_0__Nat_reprFast(x_60);
x_62 = lean_string_append(x_59, x_61);
lean_dec(x_61);
x_63 = lean_mk_string_unchecked(".lrat", 5, 5);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_45);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("bvTrace", 7, 7);
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
x_20 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_19);
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
lean_inc(x_19);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_19, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_4);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 2);
x_33 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 3);
x_34 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 4);
x_35 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 5);
x_36 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 6);
x_37 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 7);
x_38 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 8);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 9);
x_41 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 1);
lean_dec(x_25);
x_42 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_unbox(x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_43);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 2, x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 3, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 4, x_34);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 5, x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 6, x_36);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 7, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 9, x_40);
lean_inc(x_4);
x_44 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_28, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_45);
lean_inc(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed), 11, 2);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_45);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_48, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
lean_dec(x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_dec(x_45);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
x_108 = lean_st_ref_get(x_9, x_53);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_110 = lean_ctor_get(x_108, 1);
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_8, 5);
lean_inc(x_112);
x_113 = lean_unbox(x_31);
x_114 = l_Lean_SourceInfo_fromRef(x_112, x_113);
x_115 = lean_mk_string_unchecked("tactic", 6, 6);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = lean_mk_string_unchecked("bvNormalize", 11, 11);
x_118 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_117);
x_119 = lean_mk_string_unchecked("bv_normalize", 12, 12);
lean_inc(x_114);
lean_ctor_set_tag(x_108, 2);
lean_ctor_set(x_108, 1, x_119);
lean_ctor_set(x_108, 0, x_114);
x_120 = lean_mk_string_unchecked("null", 4, 4);
x_121 = l_Lean_Name_mkStr1(x_120);
x_122 = l_Array_mkArray0(lean_box(0));
lean_inc(x_114);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_114);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
lean_inc(x_114);
x_124 = l_Lean_Syntax_node1(x_114, x_21, x_123);
x_125 = l_Lean_Syntax_node2(x_114, x_118, x_108, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_box(0);
x_128 = lean_box(0);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_52);
lean_ctor_set(x_130, 2, x_52);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set(x_130, 4, x_128);
lean_ctor_set(x_130, 5, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_112);
x_132 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_133 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_55, x_130, x_131, x_132, x_52, x_6, x_7, x_8, x_9, x_110);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_131);
lean_dec(x_55);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
lean_dec(x_108);
x_135 = lean_ctor_get(x_8, 5);
lean_inc(x_135);
x_136 = lean_unbox(x_31);
x_137 = l_Lean_SourceInfo_fromRef(x_135, x_136);
x_138 = lean_mk_string_unchecked("tactic", 6, 6);
x_139 = l_Lean_Name_mkStr1(x_138);
x_140 = lean_mk_string_unchecked("bvNormalize", 11, 11);
x_141 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_140);
x_142 = lean_mk_string_unchecked("bv_normalize", 12, 12);
lean_inc(x_137);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_mk_string_unchecked("null", 4, 4);
x_145 = l_Lean_Name_mkStr1(x_144);
x_146 = l_Array_mkArray0(lean_box(0));
lean_inc(x_137);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_146);
lean_inc(x_137);
x_148 = l_Lean_Syntax_node1(x_137, x_21, x_147);
x_149 = l_Lean_Syntax_node2(x_137, x_141, x_143, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_box(0);
x_152 = lean_box(0);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_52);
lean_ctor_set(x_154, 2, x_52);
lean_ctor_set(x_154, 3, x_151);
lean_ctor_set(x_154, 4, x_152);
lean_ctor_set(x_154, 5, x_153);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_135);
x_156 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_157 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_55, x_154, x_155, x_156, x_52, x_6, x_7, x_8, x_9, x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_155);
lean_dec(x_55);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_21);
x_158 = !lean_is_exclusive(x_52);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_52, 0);
lean_dec(x_159);
x_160 = lean_ctor_get(x_45, 5);
lean_inc(x_160);
lean_dec(x_45);
x_161 = lean_ctor_get_uint8(x_160, sizeof(void*)*2);
lean_dec(x_160);
if (x_161 == 0)
{
lean_free_object(x_52);
lean_dec(x_5);
lean_dec(x_4);
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_53;
goto block_107;
}
else
{
lean_object* x_162; 
x_162 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_5);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_System_FilePath_join(x_163, x_28);
x_166 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_165, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_167);
lean_dec(x_167);
x_170 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_169, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_165, x_171, x_41, x_172);
lean_dec(x_171);
lean_dec(x_165);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_free_object(x_52);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_174;
goto block_107;
}
else
{
uint8_t x_175; 
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_175 = !lean_is_exclusive(x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_173, 0);
x_177 = lean_ctor_get(x_8, 5);
lean_inc(x_177);
lean_dec(x_8);
x_178 = lean_io_error_to_string(x_176);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_178);
x_179 = l_Lean_MessageData_ofFormat(x_52);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_173, 0, x_180);
return x_173;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_173, 0);
x_182 = lean_ctor_get(x_173, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_173);
x_183 = lean_ctor_get(x_8, 5);
lean_inc(x_183);
lean_dec(x_8);
x_184 = lean_io_error_to_string(x_181);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_184);
x_185 = l_Lean_MessageData_ofFormat(x_52);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_182);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_165);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_188 = !lean_is_exclusive(x_170);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_170, 0);
x_190 = lean_ctor_get(x_8, 5);
lean_inc(x_190);
lean_dec(x_8);
x_191 = lean_io_error_to_string(x_189);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_191);
x_192 = l_Lean_MessageData_ofFormat(x_52);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_170, 0, x_193);
return x_170;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_170, 0);
x_195 = lean_ctor_get(x_170, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_170);
x_196 = lean_ctor_get(x_8, 5);
lean_inc(x_196);
lean_dec(x_8);
x_197 = lean_io_error_to_string(x_194);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_197);
x_198 = l_Lean_MessageData_ofFormat(x_52);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_195);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_165);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_201 = !lean_is_exclusive(x_166);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_166, 0);
x_203 = lean_ctor_get(x_8, 5);
lean_inc(x_203);
lean_dec(x_8);
x_204 = lean_io_error_to_string(x_202);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_204);
x_205 = l_Lean_MessageData_ofFormat(x_52);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_166, 0, x_206);
return x_166;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_166, 0);
x_208 = lean_ctor_get(x_166, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_166);
x_209 = lean_ctor_get(x_8, 5);
lean_inc(x_209);
lean_dec(x_8);
x_210 = lean_io_error_to_string(x_207);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_210);
x_211 = l_Lean_MessageData_ofFormat(x_52);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_free_object(x_52);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_214 = !lean_is_exclusive(x_162);
if (x_214 == 0)
{
return x_162;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_162, 0);
x_216 = lean_ctor_get(x_162, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_162);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
lean_object* x_218; uint8_t x_219; 
lean_dec(x_52);
x_218 = lean_ctor_get(x_45, 5);
lean_inc(x_218);
lean_dec(x_45);
x_219 = lean_ctor_get_uint8(x_218, sizeof(void*)*2);
lean_dec(x_218);
if (x_219 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_53;
goto block_107;
}
else
{
lean_object* x_220; 
x_220 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_5);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_System_FilePath_join(x_221, x_28);
x_224 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_223, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_225);
lean_dec(x_225);
x_228 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_227, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_223, x_229, x_41, x_230);
lean_dec(x_229);
lean_dec(x_223);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_232;
goto block_107;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_235 = x_231;
} else {
 lean_dec_ref(x_231);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_8, 5);
lean_inc(x_236);
lean_dec(x_8);
x_237 = lean_io_error_to_string(x_233);
x_238 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = l_Lean_MessageData_ofFormat(x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
if (lean_is_scalar(x_235)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_235;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_234);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_223);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_242 = lean_ctor_get(x_228, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_244 = x_228;
} else {
 lean_dec_ref(x_228);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_8, 5);
lean_inc(x_245);
lean_dec(x_8);
x_246 = lean_io_error_to_string(x_242);
x_247 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l_Lean_MessageData_ofFormat(x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_248);
if (lean_is_scalar(x_244)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_244;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_223);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_251 = lean_ctor_get(x_224, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_224, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_253 = x_224;
} else {
 lean_dec_ref(x_224);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_8, 5);
lean_inc(x_254);
lean_dec(x_8);
x_255 = lean_io_error_to_string(x_251);
x_256 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = l_Lean_MessageData_ofFormat(x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
if (lean_is_scalar(x_253)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_253;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_252);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_260 = lean_ctor_get(x_220, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_220, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
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
}
}
block_107:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_st_ref_get(x_59, x_60);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_58, 5);
lean_inc(x_65);
x_66 = lean_unbox(x_31);
x_67 = l_Lean_SourceInfo_fromRef(x_65, x_66);
x_68 = lean_mk_string_unchecked("tactic", 6, 6);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = lean_mk_string_unchecked("bvCheck", 7, 7);
x_71 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_70);
x_72 = lean_mk_string_unchecked("bv_check", 8, 8);
lean_inc(x_67);
lean_ctor_set_tag(x_61, 2);
lean_ctor_set(x_61, 1, x_72);
lean_ctor_set(x_61, 0, x_67);
x_73 = lean_box(2);
x_74 = l_Lean_Syntax_mkStrLit(x_28, x_73);
lean_dec(x_28);
x_75 = l_Lean_Syntax_node3(x_67, x_71, x_61, x_19, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = lean_box(0);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_77);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_65);
x_83 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_84 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_55, x_81, x_82, x_83, x_77, x_56, x_57, x_58, x_59, x_63);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_82);
lean_dec(x_55);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
lean_dec(x_61);
x_86 = lean_ctor_get(x_58, 5);
lean_inc(x_86);
x_87 = lean_unbox(x_31);
x_88 = l_Lean_SourceInfo_fromRef(x_86, x_87);
x_89 = lean_mk_string_unchecked("tactic", 6, 6);
x_90 = l_Lean_Name_mkStr1(x_89);
x_91 = lean_mk_string_unchecked("bvCheck", 7, 7);
x_92 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_91);
x_93 = lean_mk_string_unchecked("bv_check", 8, 8);
lean_inc(x_88);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_box(2);
x_96 = l_Lean_Syntax_mkStrLit(x_28, x_95);
lean_dec(x_28);
x_97 = l_Lean_Syntax_node3(x_88, x_92, x_94, x_19, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_box(0);
x_100 = lean_box(0);
x_101 = lean_box(0);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_99);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
lean_ctor_set(x_103, 5, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_86);
x_105 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_106 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_55, x_103, x_104, x_105, x_99, x_56, x_57, x_58, x_59, x_85);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_104);
lean_dec(x_55);
return x_106;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_45);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_19);
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
x_264 = !lean_is_exclusive(x_51);
if (x_264 == 0)
{
return x_51;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_51, 0);
x_266 = lean_ctor_get(x_51, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_51);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_45);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_19);
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
x_268 = !lean_is_exclusive(x_47);
if (x_268 == 0)
{
return x_47;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_47, 0);
x_270 = lean_ctor_get(x_47, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_47);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_19);
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
x_272 = !lean_is_exclusive(x_44);
if (x_272 == 0)
{
return x_44;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_44, 0);
x_274 = lean_ctor_get(x_44, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_44);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
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
x_276 = !lean_is_exclusive(x_27);
if (x_276 == 0)
{
return x_27;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_27, 0);
x_278 = lean_ctor_get(x_27, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_27);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_21);
lean_dec(x_19);
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
x_280 = !lean_is_exclusive(x_24);
if (x_280 == 0)
{
return x_24;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_24, 0);
x_282 = lean_ctor_get(x_24, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_24);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("bvTrace", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_10 = lean_mk_string_unchecked("Frontend", 8, 8);
x_11 = lean_mk_string_unchecked("BVTrace", 7, 7);
x_12 = lean_mk_string_unchecked("evalBvTrace", 11, 11);
x_13 = l_Lean_Name_mkStr7(x_3, x_8, x_5, x_9, x_10, x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace), 10, 0);
x_15 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_13, x_14, x_1);
return x_15;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
