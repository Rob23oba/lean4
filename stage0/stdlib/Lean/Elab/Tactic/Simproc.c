// Lean compiler output
// Module: Lean.Elab.Tactic.Simproc
// Imports: Init.Simproc Lean.ReservedNameAction Lean.Meta.Tactic.Simp.Simproc Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.Term Lean.Elab.Command
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__1(uint8_t, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_unbox(x_14);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_7 = lean_box(0);
x_8 = lean_box(1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lam__0___boxed), 10, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_nat_pow(x_14, x_17);
lean_dec(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_usize(x_24, 4, x_16);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set(x_27, 6, x_26);
x_28 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7, x_28);
x_29 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 1, x_29);
x_30 = lean_unbox(x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 2, x_30);
x_31 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 3, x_31);
x_32 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 4, x_32);
x_33 = lean_unbox(x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 5, x_33);
x_34 = lean_unbox(x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 6, x_34);
x_35 = lean_unbox(x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 7, x_35);
x_36 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 8, x_36);
x_37 = lean_unbox(x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 9, x_37);
x_38 = lean_unbox(x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 10, x_38);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_25);
lean_ctor_set(x_43, 6, x_42);
x_44 = l_Lean_Elab_Term_TermElabM_run___redArg(x_9, x_27, x_43, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_elabSimprocPattern___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_elabSimprocPattern___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabSimprocPattern(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Elab_elabSimprocPattern(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Lean_Meta_simpGlobalConfig;
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_11, sizeof(void*)*1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
x_19 = lean_ctor_get(x_2, 5);
x_20 = lean_ctor_get(x_2, 6);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set_uint64(x_23, sizeof(void*)*7, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 9, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 10, x_22);
x_24 = lean_unbox(x_10);
x_25 = l_Lean_Meta_DiscrTree_mkPath(x_8, x_24, x_23, x_3, x_4, x_5, x_9);
lean_dec(x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabSimprocKeys(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_mk_string_unchecked("unexpected type at '", 20, 20);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = l_Lean_MessageData_ofName(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("', 'Simproc' expected", 21, 21);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_12, x_3, x_4, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Expr_bvar___override(x_10);
x_12 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_11, x_2, x_3, x_8);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_Expr_fvar___override(x_13);
x_15 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_14, x_2, x_3, x_8);
lean_dec(x_14);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_5);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_Expr_mvar___override(x_16);
x_18 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_17, x_2, x_3, x_8);
lean_dec(x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Expr_sort___override(x_19);
x_21 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_20, x_2, x_3, x_8);
lean_dec(x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_box(0);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_5);
x_25 = l_Lean_Expr_const___override(x_24, x_23);
x_26 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_25, x_2, x_3, x_8);
lean_dec(x_25);
return x_26;
}
case 1:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_5);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Name_str___override(x_24, x_28);
x_30 = l_Lean_Expr_const___override(x_29, x_23);
x_31 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_30, x_2, x_3, x_8);
lean_dec(x_30);
return x_31;
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
lean_inc(x_34);
x_35 = l_Lean_Name_str___override(x_24, x_34);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_free_object(x_5);
x_36 = l_Lean_Name_str___override(x_35, x_32);
x_37 = l_Lean_Expr_const___override(x_36, x_23);
x_38 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_37, x_2, x_3, x_8);
lean_dec(x_37);
return x_38;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
lean_inc(x_40);
x_41 = l_Lean_Name_str___override(x_24, x_40);
lean_inc(x_34);
x_42 = l_Lean_Name_str___override(x_41, x_34);
switch (lean_obj_tag(x_39)) {
case 0:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_34);
lean_free_object(x_5);
x_43 = l_Lean_Name_str___override(x_42, x_32);
x_44 = l_Lean_Expr_const___override(x_43, x_23);
x_45 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_44, x_2, x_3, x_8);
lean_dec(x_44);
return x_45;
}
case 1:
{
lean_object* x_46; 
lean_dec(x_42);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
switch (lean_obj_tag(x_46)) {
case 0:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_string_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_free_object(x_5);
x_50 = l_Lean_Name_str___override(x_24, x_47);
x_51 = l_Lean_Name_str___override(x_50, x_40);
x_52 = l_Lean_Name_str___override(x_51, x_34);
x_53 = l_Lean_Name_str___override(x_52, x_32);
x_54 = l_Lean_Expr_const___override(x_53, x_23);
x_55 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_54, x_2, x_3, x_8);
lean_dec(x_54);
return x_55;
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_47);
x_56 = lean_mk_string_unchecked("Meta", 4, 4);
x_57 = lean_string_dec_eq(x_40, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
lean_free_object(x_5);
x_58 = l_Lean_Name_str___override(x_24, x_48);
x_59 = l_Lean_Name_str___override(x_58, x_40);
x_60 = l_Lean_Name_str___override(x_59, x_34);
x_61 = l_Lean_Name_str___override(x_60, x_32);
x_62 = l_Lean_Expr_const___override(x_61, x_23);
x_63 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_62, x_2, x_3, x_8);
lean_dec(x_62);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_40);
x_64 = lean_mk_string_unchecked("Simp", 4, 4);
x_65 = lean_string_dec_eq(x_34, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
lean_free_object(x_5);
x_66 = l_Lean_Name_str___override(x_24, x_48);
x_67 = l_Lean_Name_str___override(x_66, x_56);
x_68 = l_Lean_Name_str___override(x_67, x_34);
x_69 = l_Lean_Name_str___override(x_68, x_32);
x_70 = l_Lean_Expr_const___override(x_69, x_23);
x_71 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_70, x_2, x_3, x_8);
lean_dec(x_70);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_34);
x_72 = lean_mk_string_unchecked("Simproc", 7, 7);
x_73 = lean_string_dec_eq(x_32, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_75 = lean_string_dec_eq(x_32, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_5);
x_76 = l_Lean_Name_str___override(x_24, x_48);
x_77 = l_Lean_Name_str___override(x_76, x_56);
x_78 = l_Lean_Name_str___override(x_77, x_64);
x_79 = l_Lean_Name_str___override(x_78, x_32);
x_80 = l_Lean_Expr_const___override(x_79, x_23);
x_81 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_80, x_2, x_3, x_8);
lean_dec(x_80);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_48);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_1);
x_82 = lean_box(x_75);
lean_ctor_set(x_5, 0, x_82);
return x_5;
}
}
else
{
lean_object* x_83; 
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_48);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_1);
x_83 = lean_box(0);
lean_ctor_set(x_5, 0, x_83);
return x_5;
}
}
}
}
}
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_5);
x_84 = lean_ctor_get(x_39, 1);
lean_inc(x_84);
lean_dec(x_39);
x_85 = lean_ctor_get(x_46, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_dec(x_46);
x_87 = l_Lean_Name_str___override(x_85, x_86);
x_88 = l_Lean_Name_str___override(x_87, x_84);
x_89 = l_Lean_Name_str___override(x_88, x_40);
x_90 = l_Lean_Name_str___override(x_89, x_34);
x_91 = l_Lean_Name_str___override(x_90, x_32);
x_92 = l_Lean_Expr_const___override(x_91, x_23);
x_93 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_92, x_2, x_3, x_8);
lean_dec(x_92);
return x_93;
}
default: 
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_5);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
lean_dec(x_39);
x_95 = lean_ctor_get(x_46, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_46, 1);
lean_inc(x_96);
lean_dec(x_46);
x_97 = l_Lean_Name_num___override(x_95, x_96);
x_98 = l_Lean_Name_str___override(x_97, x_94);
x_99 = l_Lean_Name_str___override(x_98, x_40);
x_100 = l_Lean_Name_str___override(x_99, x_34);
x_101 = l_Lean_Name_str___override(x_100, x_32);
x_102 = l_Lean_Expr_const___override(x_101, x_23);
x_103 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_102, x_2, x_3, x_8);
lean_dec(x_102);
return x_103;
}
}
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_42);
lean_free_object(x_5);
x_104 = lean_ctor_get(x_39, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_39, 1);
lean_inc(x_105);
lean_dec(x_39);
x_106 = l_Lean_Name_num___override(x_104, x_105);
x_107 = l_Lean_Name_str___override(x_106, x_40);
x_108 = l_Lean_Name_str___override(x_107, x_34);
x_109 = l_Lean_Name_str___override(x_108, x_32);
x_110 = l_Lean_Expr_const___override(x_109, x_23);
x_111 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_110, x_2, x_3, x_8);
lean_dec(x_110);
return x_111;
}
}
}
default: 
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_35);
lean_free_object(x_5);
x_112 = lean_ctor_get(x_33, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_33, 1);
lean_inc(x_113);
lean_dec(x_33);
x_114 = l_Lean_Name_num___override(x_112, x_113);
x_115 = l_Lean_Name_str___override(x_114, x_34);
x_116 = l_Lean_Name_str___override(x_115, x_32);
x_117 = l_Lean_Expr_const___override(x_116, x_23);
x_118 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_117, x_2, x_3, x_8);
lean_dec(x_117);
return x_118;
}
}
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_5);
x_119 = lean_ctor_get(x_22, 1);
lean_inc(x_119);
lean_dec(x_22);
x_120 = lean_ctor_get(x_27, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_27, 1);
lean_inc(x_121);
lean_dec(x_27);
x_122 = l_Lean_Name_num___override(x_120, x_121);
x_123 = l_Lean_Name_str___override(x_122, x_119);
x_124 = l_Lean_Expr_const___override(x_123, x_23);
x_125 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_124, x_2, x_3, x_8);
lean_dec(x_124);
return x_125;
}
}
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_free_object(x_5);
x_126 = lean_ctor_get(x_22, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_22, 1);
lean_inc(x_127);
lean_dec(x_22);
x_128 = l_Lean_Name_num___override(x_126, x_127);
x_129 = l_Lean_Expr_const___override(x_128, x_23);
x_130 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_129, x_2, x_3, x_8);
lean_dec(x_129);
return x_130;
}
}
}
case 5:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_5);
x_131 = lean_ctor_get(x_9, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_9, 1);
lean_inc(x_132);
lean_dec(x_9);
x_133 = l_Lean_Expr_app___override(x_131, x_132);
x_134 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_133, x_2, x_3, x_8);
lean_dec(x_133);
return x_134;
}
case 6:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_5);
x_135 = lean_ctor_get(x_9, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_9, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_9, 2);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_139 = l_Lean_Expr_lam___override(x_135, x_136, x_137, x_138);
x_140 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_139, x_2, x_3, x_8);
lean_dec(x_139);
return x_140;
}
case 7:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_5);
x_141 = lean_ctor_get(x_9, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_9, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_9, 2);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_145 = l_Lean_Expr_forallE___override(x_141, x_142, x_143, x_144);
x_146 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_145, x_2, x_3, x_8);
lean_dec(x_145);
return x_146;
}
case 8:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_5);
x_147 = lean_ctor_get(x_9, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_9, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_9, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_9, 3);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_9, sizeof(void*)*4 + 8);
lean_dec(x_9);
x_152 = l_Lean_Expr_letE___override(x_147, x_148, x_149, x_150, x_151);
x_153 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_152, x_2, x_3, x_8);
lean_dec(x_152);
return x_153;
}
case 9:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_5);
x_154 = lean_ctor_get(x_9, 0);
lean_inc(x_154);
lean_dec(x_9);
x_155 = l_Lean_Expr_lit___override(x_154);
x_156 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_155, x_2, x_3, x_8);
lean_dec(x_155);
return x_156;
}
case 10:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_5);
x_157 = lean_ctor_get(x_9, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_9, 1);
lean_inc(x_158);
lean_dec(x_9);
x_159 = l_Lean_Expr_mdata___override(x_157, x_158);
x_160 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_159, x_2, x_3, x_8);
lean_dec(x_159);
return x_160;
}
default: 
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_5);
x_161 = lean_ctor_get(x_9, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_9, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_9, 2);
lean_inc(x_163);
lean_dec(x_9);
x_164 = l_Lean_Expr_proj___override(x_161, x_162, x_163);
x_165 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_164, x_2, x_3, x_8);
lean_dec(x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_5, 0);
x_167 = lean_ctor_get(x_5, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_5);
x_168 = l_Lean_ConstantInfo_type(x_166);
lean_dec(x_166);
switch (lean_obj_tag(x_168)) {
case 0:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_Expr_bvar___override(x_169);
x_171 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_170, x_2, x_3, x_167);
lean_dec(x_170);
return x_171;
}
case 1:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
lean_dec(x_168);
x_173 = l_Lean_Expr_fvar___override(x_172);
x_174 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_173, x_2, x_3, x_167);
lean_dec(x_173);
return x_174;
}
case 2:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
lean_dec(x_168);
x_176 = l_Lean_Expr_mvar___override(x_175);
x_177 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_176, x_2, x_3, x_167);
lean_dec(x_176);
return x_177;
}
case 3:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_168, 0);
lean_inc(x_178);
lean_dec(x_168);
x_179 = l_Lean_Expr_sort___override(x_178);
x_180 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_179, x_2, x_3, x_167);
lean_dec(x_179);
return x_180;
}
case 4:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_168, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_168, 1);
lean_inc(x_182);
lean_dec(x_168);
x_183 = lean_box(0);
switch (lean_obj_tag(x_181)) {
case 0:
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_Lean_Expr_const___override(x_183, x_182);
x_185 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_184, x_2, x_3, x_167);
lean_dec(x_184);
return x_185;
}
case 1:
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
switch (lean_obj_tag(x_186)) {
case 0:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
lean_dec(x_181);
x_188 = l_Lean_Name_str___override(x_183, x_187);
x_189 = l_Lean_Expr_const___override(x_188, x_182);
x_190 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_189, x_2, x_3, x_167);
lean_dec(x_189);
return x_190;
}
case 1:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_181, 1);
lean_inc(x_191);
lean_dec(x_181);
x_192 = lean_ctor_get(x_186, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 1);
lean_inc(x_193);
lean_dec(x_186);
lean_inc(x_193);
x_194 = l_Lean_Name_str___override(x_183, x_193);
switch (lean_obj_tag(x_192)) {
case 0:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_193);
x_195 = l_Lean_Name_str___override(x_194, x_191);
x_196 = l_Lean_Expr_const___override(x_195, x_182);
x_197 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_196, x_2, x_3, x_167);
lean_dec(x_196);
return x_197;
}
case 1:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_194);
x_198 = lean_ctor_get(x_192, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
lean_inc(x_199);
x_200 = l_Lean_Name_str___override(x_183, x_199);
lean_inc(x_193);
x_201 = l_Lean_Name_str___override(x_200, x_193);
switch (lean_obj_tag(x_198)) {
case 0:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_199);
lean_dec(x_193);
x_202 = l_Lean_Name_str___override(x_201, x_191);
x_203 = l_Lean_Expr_const___override(x_202, x_182);
x_204 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_203, x_2, x_3, x_167);
lean_dec(x_203);
return x_204;
}
case 1:
{
lean_object* x_205; 
lean_dec(x_201);
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
switch (lean_obj_tag(x_205)) {
case 0:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_198, 1);
lean_inc(x_206);
lean_dec(x_198);
x_207 = lean_mk_string_unchecked("Lean", 4, 4);
x_208 = lean_string_dec_eq(x_206, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_207);
x_209 = l_Lean_Name_str___override(x_183, x_206);
x_210 = l_Lean_Name_str___override(x_209, x_199);
x_211 = l_Lean_Name_str___override(x_210, x_193);
x_212 = l_Lean_Name_str___override(x_211, x_191);
x_213 = l_Lean_Expr_const___override(x_212, x_182);
x_214 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_213, x_2, x_3, x_167);
lean_dec(x_213);
return x_214;
}
else
{
lean_object* x_215; uint8_t x_216; 
lean_dec(x_206);
x_215 = lean_mk_string_unchecked("Meta", 4, 4);
x_216 = lean_string_dec_eq(x_199, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_215);
x_217 = l_Lean_Name_str___override(x_183, x_207);
x_218 = l_Lean_Name_str___override(x_217, x_199);
x_219 = l_Lean_Name_str___override(x_218, x_193);
x_220 = l_Lean_Name_str___override(x_219, x_191);
x_221 = l_Lean_Expr_const___override(x_220, x_182);
x_222 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_221, x_2, x_3, x_167);
lean_dec(x_221);
return x_222;
}
else
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_199);
x_223 = lean_mk_string_unchecked("Simp", 4, 4);
x_224 = lean_string_dec_eq(x_193, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_223);
x_225 = l_Lean_Name_str___override(x_183, x_207);
x_226 = l_Lean_Name_str___override(x_225, x_215);
x_227 = l_Lean_Name_str___override(x_226, x_193);
x_228 = l_Lean_Name_str___override(x_227, x_191);
x_229 = l_Lean_Expr_const___override(x_228, x_182);
x_230 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_229, x_2, x_3, x_167);
lean_dec(x_229);
return x_230;
}
else
{
lean_object* x_231; uint8_t x_232; 
lean_dec(x_193);
x_231 = lean_mk_string_unchecked("Simproc", 7, 7);
x_232 = lean_string_dec_eq(x_191, x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_234 = lean_string_dec_eq(x_191, x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_235 = l_Lean_Name_str___override(x_183, x_207);
x_236 = l_Lean_Name_str___override(x_235, x_215);
x_237 = l_Lean_Name_str___override(x_236, x_223);
x_238 = l_Lean_Name_str___override(x_237, x_191);
x_239 = l_Lean_Expr_const___override(x_238, x_182);
x_240 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_239, x_2, x_3, x_167);
lean_dec(x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_223);
lean_dec(x_215);
lean_dec(x_207);
lean_dec(x_191);
lean_dec(x_182);
lean_dec(x_1);
x_241 = lean_box(x_234);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_167);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_223);
lean_dec(x_215);
lean_dec(x_207);
lean_dec(x_191);
lean_dec(x_182);
lean_dec(x_1);
x_243 = lean_box(0);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_167);
return x_244;
}
}
}
}
}
case 1:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_245 = lean_ctor_get(x_198, 1);
lean_inc(x_245);
lean_dec(x_198);
x_246 = lean_ctor_get(x_205, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_205, 1);
lean_inc(x_247);
lean_dec(x_205);
x_248 = l_Lean_Name_str___override(x_246, x_247);
x_249 = l_Lean_Name_str___override(x_248, x_245);
x_250 = l_Lean_Name_str___override(x_249, x_199);
x_251 = l_Lean_Name_str___override(x_250, x_193);
x_252 = l_Lean_Name_str___override(x_251, x_191);
x_253 = l_Lean_Expr_const___override(x_252, x_182);
x_254 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_253, x_2, x_3, x_167);
lean_dec(x_253);
return x_254;
}
default: 
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_255 = lean_ctor_get(x_198, 1);
lean_inc(x_255);
lean_dec(x_198);
x_256 = lean_ctor_get(x_205, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_205, 1);
lean_inc(x_257);
lean_dec(x_205);
x_258 = l_Lean_Name_num___override(x_256, x_257);
x_259 = l_Lean_Name_str___override(x_258, x_255);
x_260 = l_Lean_Name_str___override(x_259, x_199);
x_261 = l_Lean_Name_str___override(x_260, x_193);
x_262 = l_Lean_Name_str___override(x_261, x_191);
x_263 = l_Lean_Expr_const___override(x_262, x_182);
x_264 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_263, x_2, x_3, x_167);
lean_dec(x_263);
return x_264;
}
}
}
default: 
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_201);
x_265 = lean_ctor_get(x_198, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_198, 1);
lean_inc(x_266);
lean_dec(x_198);
x_267 = l_Lean_Name_num___override(x_265, x_266);
x_268 = l_Lean_Name_str___override(x_267, x_199);
x_269 = l_Lean_Name_str___override(x_268, x_193);
x_270 = l_Lean_Name_str___override(x_269, x_191);
x_271 = l_Lean_Expr_const___override(x_270, x_182);
x_272 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_271, x_2, x_3, x_167);
lean_dec(x_271);
return x_272;
}
}
}
default: 
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_194);
x_273 = lean_ctor_get(x_192, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_192, 1);
lean_inc(x_274);
lean_dec(x_192);
x_275 = l_Lean_Name_num___override(x_273, x_274);
x_276 = l_Lean_Name_str___override(x_275, x_193);
x_277 = l_Lean_Name_str___override(x_276, x_191);
x_278 = l_Lean_Expr_const___override(x_277, x_182);
x_279 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_278, x_2, x_3, x_167);
lean_dec(x_278);
return x_279;
}
}
}
default: 
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_280 = lean_ctor_get(x_181, 1);
lean_inc(x_280);
lean_dec(x_181);
x_281 = lean_ctor_get(x_186, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_186, 1);
lean_inc(x_282);
lean_dec(x_186);
x_283 = l_Lean_Name_num___override(x_281, x_282);
x_284 = l_Lean_Name_str___override(x_283, x_280);
x_285 = l_Lean_Expr_const___override(x_284, x_182);
x_286 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_285, x_2, x_3, x_167);
lean_dec(x_285);
return x_286;
}
}
}
default: 
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_181, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_181, 1);
lean_inc(x_288);
lean_dec(x_181);
x_289 = l_Lean_Name_num___override(x_287, x_288);
x_290 = l_Lean_Expr_const___override(x_289, x_182);
x_291 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_290, x_2, x_3, x_167);
lean_dec(x_290);
return x_291;
}
}
}
case 5:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_168, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_168, 1);
lean_inc(x_293);
lean_dec(x_168);
x_294 = l_Lean_Expr_app___override(x_292, x_293);
x_295 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_294, x_2, x_3, x_167);
lean_dec(x_294);
return x_295;
}
case 6:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_168, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_168, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_168, 2);
lean_inc(x_298);
x_299 = lean_ctor_get_uint8(x_168, sizeof(void*)*3 + 8);
lean_dec(x_168);
x_300 = l_Lean_Expr_lam___override(x_296, x_297, x_298, x_299);
x_301 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_300, x_2, x_3, x_167);
lean_dec(x_300);
return x_301;
}
case 7:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_168, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_168, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_168, 2);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_168, sizeof(void*)*3 + 8);
lean_dec(x_168);
x_306 = l_Lean_Expr_forallE___override(x_302, x_303, x_304, x_305);
x_307 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_306, x_2, x_3, x_167);
lean_dec(x_306);
return x_307;
}
case 8:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_168, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_168, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_168, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_168, 3);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_168, sizeof(void*)*4 + 8);
lean_dec(x_168);
x_313 = l_Lean_Expr_letE___override(x_308, x_309, x_310, x_311, x_312);
x_314 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_313, x_2, x_3, x_167);
lean_dec(x_313);
return x_314;
}
case 9:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_168, 0);
lean_inc(x_315);
lean_dec(x_168);
x_316 = l_Lean_Expr_lit___override(x_315);
x_317 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_316, x_2, x_3, x_167);
lean_dec(x_316);
return x_317;
}
case 10:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_168, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_168, 1);
lean_inc(x_319);
lean_dec(x_168);
x_320 = l_Lean_Expr_mdata___override(x_318, x_319);
x_321 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_320, x_2, x_3, x_167);
lean_dec(x_320);
return x_321;
}
default: 
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_168, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_168, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_168, 2);
lean_inc(x_324);
lean_dec(x_168);
x_325 = l_Lean_Expr_proj___override(x_322, x_323, x_324);
x_326 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_325, x_2, x_3, x_167);
lean_dec(x_325);
return x_326;
}
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_1);
x_327 = !lean_is_exclusive(x_5);
if (x_327 == 0)
{
return x_5;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_5, 0);
x_329 = lean_ctor_get(x_5, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_5);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSimprocType___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSimprocType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_realizeGlobalConstNoOverload(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_checkSimprocType(x_11, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_elabSimprocKeys(x_2, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Simp_registerSimproc(x_11, x_16, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("simprocPattern", 14, 14);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed), 9, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
x_16 = l_Lean_Elab_Command_liftTermElabM___redArg(x_15, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSimprocPattern___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPattern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("simprocPattern", 14, 14);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Command", 7, 7);
x_9 = lean_mk_string_unchecked("elabSimprocPattern", 18, 18);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabSimprocPattern", 18, 18);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(39u);
x_8 = lean_unsigned_to_nat(51u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(45u);
x_11 = lean_unsigned_to_nat(33u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(55u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(73u);
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
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Meta", 4, 4);
x_14 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_15 = lean_mk_string_unchecked("Key", 3, 3);
x_16 = lean_mk_string_unchecked("const", 5, 5);
x_17 = l_Lean_Name_mkStr5(x_12, x_13, x_14, x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_17, x_18);
x_20 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_10);
x_21 = l_Lean_mkNatLit(x_11);
x_22 = l_Lean_mkAppB(x_19, x_20, x_21);
x_6 = x_22;
goto block_9;
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Meta", 4, 4);
x_27 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_28 = lean_mk_string_unchecked("Key", 3, 3);
x_29 = lean_mk_string_unchecked("fvar", 4, 4);
lean_inc(x_25);
x_30 = l_Lean_Name_mkStr5(x_25, x_26, x_27, x_28, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Expr_const___override(x_30, x_31);
x_33 = lean_mk_string_unchecked("FVarId", 6, 6);
x_34 = lean_mk_string_unchecked("mk", 2, 2);
x_35 = l_Lean_Name_mkStr3(x_25, x_33, x_34);
x_36 = l_Lean_Expr_const___override(x_35, x_31);
x_37 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_23);
x_38 = l_Lean_Expr_app___override(x_36, x_37);
x_39 = l_Lean_mkNatLit(x_24);
x_40 = l_Lean_mkAppB(x_32, x_38, x_39);
x_6 = x_40;
goto block_9;
}
case 2:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_mk_string_unchecked("Lean", 4, 4);
x_43 = lean_mk_string_unchecked("Meta", 4, 4);
x_44 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_45 = lean_mk_string_unchecked("Key", 3, 3);
x_46 = lean_mk_string_unchecked("lit", 3, 3);
lean_inc(x_42);
x_47 = l_Lean_Name_mkStr5(x_42, x_43, x_44, x_45, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_mk_string_unchecked("Literal", 7, 7);
x_51 = lean_mk_string_unchecked("natVal", 6, 6);
x_52 = l_Lean_Name_mkStr3(x_42, x_50, x_51);
x_53 = l_Lean_Expr_const___override(x_52, x_48);
x_54 = l_Lean_Expr_lit___override(x_41);
x_55 = l_Lean_Expr_app___override(x_53, x_54);
x_56 = l_Lean_Expr_app___override(x_49, x_55);
x_6 = x_56;
goto block_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_mk_string_unchecked("Literal", 7, 7);
x_58 = lean_mk_string_unchecked("strVal", 6, 6);
x_59 = l_Lean_Name_mkStr3(x_42, x_57, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_48);
x_61 = l_Lean_Expr_lit___override(x_41);
x_62 = l_Lean_Expr_app___override(x_60, x_61);
x_63 = l_Lean_Expr_app___override(x_49, x_62);
x_6 = x_63;
goto block_9;
}
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Meta", 4, 4);
x_66 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_67 = lean_mk_string_unchecked("Key", 3, 3);
x_68 = lean_mk_string_unchecked("star", 4, 4);
x_69 = l_Lean_Name_mkStr5(x_64, x_65, x_66, x_67, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Expr_const___override(x_69, x_70);
x_6 = x_71;
goto block_9;
}
case 4:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Meta", 4, 4);
x_74 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_75 = lean_mk_string_unchecked("Key", 3, 3);
x_76 = lean_mk_string_unchecked("other", 5, 5);
x_77 = l_Lean_Name_mkStr5(x_72, x_73, x_74, x_75, x_76);
x_78 = lean_box(0);
x_79 = l_Lean_Expr_const___override(x_77, x_78);
x_6 = x_79;
goto block_9;
}
case 5:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Meta", 4, 4);
x_82 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_83 = lean_mk_string_unchecked("Key", 3, 3);
x_84 = lean_mk_string_unchecked("arrow", 5, 5);
x_85 = l_Lean_Name_mkStr5(x_80, x_81, x_82, x_83, x_84);
x_86 = lean_box(0);
x_87 = l_Lean_Expr_const___override(x_85, x_86);
x_6 = x_87;
goto block_9;
}
default: 
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_4, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 2);
lean_inc(x_90);
lean_dec(x_4);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Meta", 4, 4);
x_93 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_94 = lean_mk_string_unchecked("Key", 3, 3);
x_95 = lean_mk_string_unchecked("proj", 4, 4);
x_96 = l_Lean_Name_mkStr5(x_91, x_92, x_93, x_94, x_95);
x_97 = lean_box(0);
x_98 = l_Lean_Expr_const___override(x_96, x_97);
x_99 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_88);
x_100 = l_Lean_mkNatLit(x_89);
x_101 = l_Lean_mkNatLit(x_90);
x_102 = l_Lean_mkApp3(x_98, x_99, x_100, x_101);
x_6 = x_102;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_1, x_2, x_5);
x_8 = l_Lean_mkAppB(x_2, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
x_12 = l_Lean_realizeGlobalConstNoOverload(x_1, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Elab_checkSimprocType(x_13, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Elab_elabSimprocKeys(x_2, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_61; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_61 = lean_unbox(x_16);
lean_dec(x_16);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_mk_string_unchecked("Meta", 4, 4);
x_63 = lean_mk_string_unchecked("Simp", 4, 4);
x_64 = lean_mk_string_unchecked("registerBuiltinSimproc", 22, 22);
lean_inc(x_3);
x_65 = l_Lean_Name_mkStr4(x_3, x_62, x_63, x_64);
x_21 = x_65;
goto block_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_mk_string_unchecked("Meta", 4, 4);
x_67 = lean_mk_string_unchecked("Simp", 4, 4);
x_68 = lean_mk_string_unchecked("registerBuiltinDSimproc", 23, 23);
lean_inc(x_3);
x_69 = l_Lean_Name_mkStr4(x_3, x_66, x_67, x_68);
x_21 = x_69;
goto block_60;
}
block_60:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_22 = lean_box(0);
lean_inc(x_13);
x_23 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_13);
x_24 = lean_mk_string_unchecked("Meta", 4, 4);
x_25 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_26 = lean_mk_string_unchecked("Key", 3, 3);
x_27 = l_Lean_Name_mkStr4(x_3, x_24, x_25, x_26);
x_28 = l_Lean_Expr_const___override(x_27, x_22);
x_29 = lean_mk_string_unchecked("List", 4, 4);
x_30 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_29);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_22);
lean_inc(x_33);
x_34 = l_Lean_Expr_const___override(x_31, x_33);
x_35 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_29);
x_36 = l_Lean_Name_mkStr2(x_29, x_35);
lean_inc(x_33);
x_37 = l_Lean_Expr_const___override(x_36, x_33);
lean_inc(x_28);
x_38 = l_Lean_Expr_app___override(x_37, x_28);
x_39 = lean_mk_string_unchecked("cons", 4, 4);
x_40 = l_Lean_Name_mkStr2(x_29, x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_33);
lean_inc(x_28);
x_42 = l_Lean_Expr_app___override(x_41, x_28);
x_43 = lean_array_to_list(x_19);
x_44 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_38, x_42, x_43);
lean_dec(x_38);
x_45 = l_Lean_mkAppB(x_34, x_28, x_44);
x_46 = lean_mk_empty_array_with_capacity(x_4);
x_47 = lean_array_push(x_46, x_23);
x_48 = lean_mk_string_unchecked("declare", 7, 7);
x_49 = l_Lean_Name_mkStr1(x_48);
lean_inc(x_13);
x_50 = l_Lean_Name_append(x_13, x_49);
x_51 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_50, x_9, x_10, x_20);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Expr_const___override(x_13, x_22);
x_55 = lean_array_push(x_47, x_45);
x_56 = l_Lean_Expr_const___override(x_21, x_22);
x_57 = lean_array_push(x_55, x_54);
x_58 = l_Lean_mkAppN(x_56, x_57);
lean_dec(x_57);
x_59 = l_Lean_declareBuiltin(x_52, x_58, x_9, x_10, x_53);
return x_59;
}
}
else
{
uint8_t x_70; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_18);
if (x_70 == 0)
{
return x_18;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_18, 0);
x_72 = lean_ctor_get(x_18, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("simprocPatternBuiltin", 21, 21);
lean_inc(x_5);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed), 11, 4);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_13);
x_16 = l_Lean_Elab_Command_liftTermElabM___redArg(x_15, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSimprocPatternBuiltin(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("simprocPatternBuiltin", 21, 21);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Command", 7, 7);
x_9 = lean_mk_string_unchecked("elabSimprocPatternBuiltin", 25, 25);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabSimprocPatternBuiltin", 25, 25);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(47u);
x_8 = lean_unsigned_to_nat(58u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(56u);
x_11 = lean_unsigned_to_nat(35u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(62u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(87u);
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
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
