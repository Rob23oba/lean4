// Lean compiler output
// Module: Lake.DSL.VerLit
// Imports: Lean.Elab.Eval Lake.Util.Version Lake.DSL.Syntax
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
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprStdVer;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_toResultExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprStdVer___lam__0(lean_object*);
lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabVerLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lake_elabVerLit__1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprSemVerCore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_toResultExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabVerLit_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprSemVerCore;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprSemVerCore___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("SemVerCore", 10, 10);
x_4 = lean_mk_string_unchecked("mk", 2, 2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_mkNatLit(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_mkNatLit(x_10);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkNatLit(x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_11);
x_18 = lean_array_push(x_17, x_13);
x_19 = l_Lean_mkAppN(x_7, x_18);
lean_dec(x_18);
return x_19;
}
}
static lean_object* _init_l_Lake_instToExprSemVerCore() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToExprSemVerCore___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("SemVerCore", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instToExprStdVer___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("StdVer", 6, 6);
x_4 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("SemVerCore", 10, 10);
x_10 = l_Lean_Name_mkStr3(x_2, x_9, x_4);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = l_Lean_mkNatLit(x_12);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = l_Lean_mkNatLit(x_14);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_mkNatLit(x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_17);
x_23 = l_Lean_mkAppN(x_11, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_mkStrLit(x_24);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_array_push(x_27, x_23);
x_29 = lean_array_push(x_28, x_25);
x_30 = l_Lean_mkAppN(x_7, x_29);
lean_dec(x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_instToExprStdVer() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToExprStdVer___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("StdVer", 6, 6);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_toResultExpr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_apply_1(x_6, x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_1(x_6, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_toResultExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_DSL_VerLit_0__Lake_toResultExpr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_elabVerLit_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_evalExpr(lean_box(0), x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_elabVerLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_mk_string_unchecked("Lake", 4, 4);
x_11 = lean_mk_string_unchecked("verLit", 6, 6);
lean_inc(x_10);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("expected type is not known", 26, 26);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_mk_string_unchecked("Except", 6, 6);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("String", 6, 6);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_28);
lean_inc(x_31);
x_32 = lean_array_push(x_31, x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_33 = l_Lean_Meta_mkAppM(x_24, x_32, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_st_ref_get(x_8, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_ctor_get(x_7, 5);
lean_inc(x_42);
x_43 = lean_box(0);
x_44 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_45 = lean_unbox(x_43);
x_46 = l_Lean_SourceInfo_fromRef(x_42, x_45);
lean_dec(x_42);
x_47 = lean_ctor_get(x_7, 10);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_Lean_Environment_mainModule(x_48);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Parser", 6, 6);
x_52 = lean_mk_string_unchecked("Term", 4, 4);
x_53 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_50);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
x_55 = lean_mk_string_unchecked("decodeVersion", 13, 13);
lean_inc(x_55);
x_56 = l_String_toSubstring_x27(x_55);
lean_inc(x_55);
x_57 = l_Lean_Name_mkStr1(x_55);
x_58 = l_Lean_addMacroScope(x_49, x_57, x_47);
x_59 = lean_mk_string_unchecked("DecodeVersion", 13, 13);
lean_inc(x_10);
x_60 = l_Lean_Name_mkStr3(x_10, x_59, x_55);
x_61 = lean_box(0);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_61);
lean_ctor_set(x_37, 0, x_60);
x_62 = lean_box(0);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_62);
lean_ctor_set(x_33, 0, x_37);
lean_inc(x_46);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_33);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = lean_mk_string_unchecked("termS!_", 7, 7);
x_67 = l_Lean_Name_mkStr1(x_66);
x_68 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_46);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_46);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_46);
x_70 = l_Lean_Syntax_node2(x_46, x_67, x_69, x_44);
lean_inc(x_46);
x_71 = l_Lean_Syntax_node1(x_46, x_65, x_70);
x_72 = l_Lean_Syntax_node2(x_46, x_54, x_63, x_71);
lean_ctor_set(x_2, 0, x_35);
x_73 = lean_box(0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_74 = l_Lean_Elab_Term_elabTermEnsuringType(x_72, x_2, x_13, x_13, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_mk_string_unchecked("Expr", 4, 4);
x_78 = l_Lean_Name_mkStr2(x_50, x_77);
x_79 = l_Lean_Expr_const___override(x_78, x_27);
x_80 = lean_array_push(x_31, x_79);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Meta_mkAppM(x_24, x_80, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_box(0);
x_86 = lean_mk_string_unchecked("_private", 8, 8);
x_87 = l_Lean_Name_str___override(x_85, x_86);
lean_inc(x_10);
x_88 = l_Lean_Name_str___override(x_87, x_10);
x_89 = lean_mk_string_unchecked("DSL", 3, 3);
x_90 = l_Lean_Name_str___override(x_88, x_89);
x_91 = lean_mk_string_unchecked("VerLit", 6, 6);
x_92 = l_Lean_Name_str___override(x_90, x_91);
x_93 = l_Lean_Name_num___override(x_92, x_84);
x_94 = l_Lean_Name_str___override(x_93, x_10);
x_95 = lean_mk_string_unchecked("toResultExpr", 12, 12);
x_96 = l_Lean_Name_str___override(x_94, x_95);
x_97 = lean_mk_empty_array_with_capacity(x_41);
x_98 = lean_array_push(x_97, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_99 = l_Lean_Meta_mkAppM(x_96, x_98, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = l_Lake_elabVerLit_unsafe__1(x_82, x_100, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = !lean_is_exclusive(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_ctor_set_tag(x_103, 3);
x_106 = l_Lean_MessageData_ofFormat(x_103);
x_107 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_Lean_MessageData_ofFormat(x_109);
x_111 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_110, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_102);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_102, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
lean_dec(x_103);
lean_ctor_set(x_102, 0, x_114);
return x_102;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_102, 1);
lean_inc(x_115);
lean_dec(x_102);
x_116 = lean_ctor_get(x_103, 0);
lean_inc(x_116);
lean_dec(x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_102);
if (x_118 == 0)
{
return x_102;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_102, 0);
x_120 = lean_ctor_get(x_102, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_102);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_99;
}
}
else
{
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_81;
}
}
else
{
lean_dec(x_50);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_74;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_122 = lean_ctor_get(x_37, 0);
x_123 = lean_ctor_get(x_37, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_37);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_ctor_get(x_7, 5);
lean_inc(x_125);
x_126 = lean_box(0);
x_127 = l_Lean_Syntax_getArg(x_1, x_124);
lean_dec(x_1);
x_128 = lean_unbox(x_126);
x_129 = l_Lean_SourceInfo_fromRef(x_125, x_128);
lean_dec(x_125);
x_130 = lean_ctor_get(x_7, 10);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 0);
lean_inc(x_131);
lean_dec(x_122);
x_132 = l_Lean_Environment_mainModule(x_131);
lean_dec(x_131);
x_133 = lean_mk_string_unchecked("Lean", 4, 4);
x_134 = lean_mk_string_unchecked("Parser", 6, 6);
x_135 = lean_mk_string_unchecked("Term", 4, 4);
x_136 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_133);
x_137 = l_Lean_Name_mkStr4(x_133, x_134, x_135, x_136);
x_138 = lean_mk_string_unchecked("decodeVersion", 13, 13);
lean_inc(x_138);
x_139 = l_String_toSubstring_x27(x_138);
lean_inc(x_138);
x_140 = l_Lean_Name_mkStr1(x_138);
x_141 = l_Lean_addMacroScope(x_132, x_140, x_130);
x_142 = lean_mk_string_unchecked("DecodeVersion", 13, 13);
lean_inc(x_10);
x_143 = l_Lean_Name_mkStr3(x_10, x_142, x_138);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_box(0);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_146);
lean_ctor_set(x_33, 0, x_145);
lean_inc(x_129);
x_147 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_147, 0, x_129);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_141);
lean_ctor_set(x_147, 3, x_33);
x_148 = lean_mk_string_unchecked("null", 4, 4);
x_149 = l_Lean_Name_mkStr1(x_148);
x_150 = lean_mk_string_unchecked("termS!_", 7, 7);
x_151 = l_Lean_Name_mkStr1(x_150);
x_152 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_129);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_129);
lean_ctor_set(x_153, 1, x_152);
lean_inc(x_129);
x_154 = l_Lean_Syntax_node2(x_129, x_151, x_153, x_127);
lean_inc(x_129);
x_155 = l_Lean_Syntax_node1(x_129, x_149, x_154);
x_156 = l_Lean_Syntax_node2(x_129, x_137, x_147, x_155);
lean_ctor_set(x_2, 0, x_35);
x_157 = lean_box(0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_158 = l_Lean_Elab_Term_elabTermEnsuringType(x_156, x_2, x_13, x_13, x_157, x_3, x_4, x_5, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_mk_string_unchecked("Expr", 4, 4);
x_162 = l_Lean_Name_mkStr2(x_133, x_161);
x_163 = l_Lean_Expr_const___override(x_162, x_27);
x_164 = lean_array_push(x_31, x_163);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_165 = l_Lean_Meta_mkAppM(x_24, x_164, x_5, x_6, x_7, x_8, x_160);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_unsigned_to_nat(0u);
x_169 = lean_box(0);
x_170 = lean_mk_string_unchecked("_private", 8, 8);
x_171 = l_Lean_Name_str___override(x_169, x_170);
lean_inc(x_10);
x_172 = l_Lean_Name_str___override(x_171, x_10);
x_173 = lean_mk_string_unchecked("DSL", 3, 3);
x_174 = l_Lean_Name_str___override(x_172, x_173);
x_175 = lean_mk_string_unchecked("VerLit", 6, 6);
x_176 = l_Lean_Name_str___override(x_174, x_175);
x_177 = l_Lean_Name_num___override(x_176, x_168);
x_178 = l_Lean_Name_str___override(x_177, x_10);
x_179 = lean_mk_string_unchecked("toResultExpr", 12, 12);
x_180 = l_Lean_Name_str___override(x_178, x_179);
x_181 = lean_mk_empty_array_with_capacity(x_124);
x_182 = lean_array_push(x_181, x_159);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_183 = l_Lean_Meta_mkAppM(x_180, x_182, x_5, x_6, x_7, x_8, x_167);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_186 = l_Lake_elabVerLit_unsafe__1(x_166, x_184, x_5, x_6, x_7, x_8, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(3, 1, 0);
} else {
 x_191 = x_190;
 lean_ctor_set_tag(x_191, 3);
}
lean_ctor_set(x_191, 0, x_189);
x_192 = l_Lean_MessageData_ofFormat(x_191);
x_193 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_188);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_187, 0);
lean_inc(x_196);
lean_dec(x_187);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_198 = lean_ctor_get(x_186, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_186, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_200 = x_186;
} else {
 lean_dec_ref(x_186);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_dec(x_166);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_183;
}
}
else
{
lean_dec(x_159);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_165;
}
}
else
{
lean_dec(x_133);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_158;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_202 = lean_ctor_get(x_33, 0);
x_203 = lean_ctor_get(x_33, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_33);
x_204 = lean_st_ref_get(x_8, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_ctor_get(x_7, 5);
lean_inc(x_209);
x_210 = lean_box(0);
x_211 = l_Lean_Syntax_getArg(x_1, x_208);
lean_dec(x_1);
x_212 = lean_unbox(x_210);
x_213 = l_Lean_SourceInfo_fromRef(x_209, x_212);
lean_dec(x_209);
x_214 = lean_ctor_get(x_7, 10);
lean_inc(x_214);
x_215 = lean_ctor_get(x_205, 0);
lean_inc(x_215);
lean_dec(x_205);
x_216 = l_Lean_Environment_mainModule(x_215);
lean_dec(x_215);
x_217 = lean_mk_string_unchecked("Lean", 4, 4);
x_218 = lean_mk_string_unchecked("Parser", 6, 6);
x_219 = lean_mk_string_unchecked("Term", 4, 4);
x_220 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_217);
x_221 = l_Lean_Name_mkStr4(x_217, x_218, x_219, x_220);
x_222 = lean_mk_string_unchecked("decodeVersion", 13, 13);
lean_inc(x_222);
x_223 = l_String_toSubstring_x27(x_222);
lean_inc(x_222);
x_224 = l_Lean_Name_mkStr1(x_222);
x_225 = l_Lean_addMacroScope(x_216, x_224, x_214);
x_226 = lean_mk_string_unchecked("DecodeVersion", 13, 13);
lean_inc(x_10);
x_227 = l_Lean_Name_mkStr3(x_10, x_226, x_222);
x_228 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_207;
 lean_ctor_set_tag(x_229, 1);
}
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_box(0);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
lean_inc(x_213);
x_232 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_232, 0, x_213);
lean_ctor_set(x_232, 1, x_223);
lean_ctor_set(x_232, 2, x_225);
lean_ctor_set(x_232, 3, x_231);
x_233 = lean_mk_string_unchecked("null", 4, 4);
x_234 = l_Lean_Name_mkStr1(x_233);
x_235 = lean_mk_string_unchecked("termS!_", 7, 7);
x_236 = l_Lean_Name_mkStr1(x_235);
x_237 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_213);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_213);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_213);
x_239 = l_Lean_Syntax_node2(x_213, x_236, x_238, x_211);
lean_inc(x_213);
x_240 = l_Lean_Syntax_node1(x_213, x_234, x_239);
x_241 = l_Lean_Syntax_node2(x_213, x_221, x_232, x_240);
lean_ctor_set(x_2, 0, x_202);
x_242 = lean_box(0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_243 = l_Lean_Elab_Term_elabTermEnsuringType(x_241, x_2, x_13, x_13, x_242, x_3, x_4, x_5, x_6, x_7, x_8, x_206);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_mk_string_unchecked("Expr", 4, 4);
x_247 = l_Lean_Name_mkStr2(x_217, x_246);
x_248 = l_Lean_Expr_const___override(x_247, x_27);
x_249 = lean_array_push(x_31, x_248);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_250 = l_Lean_Meta_mkAppM(x_24, x_249, x_5, x_6, x_7, x_8, x_245);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_unsigned_to_nat(0u);
x_254 = lean_box(0);
x_255 = lean_mk_string_unchecked("_private", 8, 8);
x_256 = l_Lean_Name_str___override(x_254, x_255);
lean_inc(x_10);
x_257 = l_Lean_Name_str___override(x_256, x_10);
x_258 = lean_mk_string_unchecked("DSL", 3, 3);
x_259 = l_Lean_Name_str___override(x_257, x_258);
x_260 = lean_mk_string_unchecked("VerLit", 6, 6);
x_261 = l_Lean_Name_str___override(x_259, x_260);
x_262 = l_Lean_Name_num___override(x_261, x_253);
x_263 = l_Lean_Name_str___override(x_262, x_10);
x_264 = lean_mk_string_unchecked("toResultExpr", 12, 12);
x_265 = l_Lean_Name_str___override(x_263, x_264);
x_266 = lean_mk_empty_array_with_capacity(x_208);
x_267 = lean_array_push(x_266, x_244);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_268 = l_Lean_Meta_mkAppM(x_265, x_267, x_5, x_6, x_7, x_8, x_252);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_271 = l_Lake_elabVerLit_unsafe__1(x_251, x_269, x_5, x_6, x_7, x_8, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(3, 1, 0);
} else {
 x_276 = x_275;
 lean_ctor_set_tag(x_276, 3);
}
lean_ctor_set(x_276, 0, x_274);
x_277 = l_Lean_MessageData_ofFormat(x_276);
x_278 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_277, x_3, x_4, x_5, x_6, x_7, x_8, x_273);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_279 = lean_ctor_get(x_271, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_280 = x_271;
} else {
 lean_dec_ref(x_271);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
lean_dec(x_272);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_283 = lean_ctor_get(x_271, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_271, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_285 = x_271;
} else {
 lean_dec_ref(x_271);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_dec(x_251);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_268;
}
}
else
{
lean_dec(x_244);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_250;
}
}
else
{
lean_dec(x_217);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_243;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_24);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_33;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_287 = lean_ctor_get(x_2, 0);
lean_inc(x_287);
lean_dec(x_2);
x_288 = lean_mk_string_unchecked("Except", 6, 6);
x_289 = l_Lean_Name_mkStr1(x_288);
x_290 = lean_mk_string_unchecked("String", 6, 6);
x_291 = l_Lean_Name_mkStr1(x_290);
x_292 = lean_box(0);
x_293 = l_Lean_Expr_const___override(x_291, x_292);
x_294 = lean_unsigned_to_nat(2u);
x_295 = lean_mk_empty_array_with_capacity(x_294);
x_296 = lean_array_push(x_295, x_293);
lean_inc(x_296);
x_297 = lean_array_push(x_296, x_287);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_289);
x_298 = l_Lean_Meta_mkAppM(x_289, x_297, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_st_ref_get(x_8, x_300);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_ctor_get(x_7, 5);
lean_inc(x_307);
x_308 = lean_box(0);
x_309 = l_Lean_Syntax_getArg(x_1, x_306);
lean_dec(x_1);
x_310 = lean_unbox(x_308);
x_311 = l_Lean_SourceInfo_fromRef(x_307, x_310);
lean_dec(x_307);
x_312 = lean_ctor_get(x_7, 10);
lean_inc(x_312);
x_313 = lean_ctor_get(x_303, 0);
lean_inc(x_313);
lean_dec(x_303);
x_314 = l_Lean_Environment_mainModule(x_313);
lean_dec(x_313);
x_315 = lean_mk_string_unchecked("Lean", 4, 4);
x_316 = lean_mk_string_unchecked("Parser", 6, 6);
x_317 = lean_mk_string_unchecked("Term", 4, 4);
x_318 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_315);
x_319 = l_Lean_Name_mkStr4(x_315, x_316, x_317, x_318);
x_320 = lean_mk_string_unchecked("decodeVersion", 13, 13);
lean_inc(x_320);
x_321 = l_String_toSubstring_x27(x_320);
lean_inc(x_320);
x_322 = l_Lean_Name_mkStr1(x_320);
x_323 = l_Lean_addMacroScope(x_314, x_322, x_312);
x_324 = lean_mk_string_unchecked("DecodeVersion", 13, 13);
lean_inc(x_10);
x_325 = l_Lean_Name_mkStr3(x_10, x_324, x_320);
x_326 = lean_box(0);
if (lean_is_scalar(x_305)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_305;
 lean_ctor_set_tag(x_327, 1);
}
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_box(0);
if (lean_is_scalar(x_301)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_301;
 lean_ctor_set_tag(x_329, 1);
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
lean_inc(x_311);
x_330 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_330, 0, x_311);
lean_ctor_set(x_330, 1, x_321);
lean_ctor_set(x_330, 2, x_323);
lean_ctor_set(x_330, 3, x_329);
x_331 = lean_mk_string_unchecked("null", 4, 4);
x_332 = l_Lean_Name_mkStr1(x_331);
x_333 = lean_mk_string_unchecked("termS!_", 7, 7);
x_334 = l_Lean_Name_mkStr1(x_333);
x_335 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_311);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_311);
lean_ctor_set(x_336, 1, x_335);
lean_inc(x_311);
x_337 = l_Lean_Syntax_node2(x_311, x_334, x_336, x_309);
lean_inc(x_311);
x_338 = l_Lean_Syntax_node1(x_311, x_332, x_337);
x_339 = l_Lean_Syntax_node2(x_311, x_319, x_330, x_338);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_299);
x_341 = lean_box(0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_342 = l_Lean_Elab_Term_elabTermEnsuringType(x_339, x_340, x_13, x_13, x_341, x_3, x_4, x_5, x_6, x_7, x_8, x_304);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_mk_string_unchecked("Expr", 4, 4);
x_346 = l_Lean_Name_mkStr2(x_315, x_345);
x_347 = l_Lean_Expr_const___override(x_346, x_292);
x_348 = lean_array_push(x_296, x_347);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_349 = l_Lean_Meta_mkAppM(x_289, x_348, x_5, x_6, x_7, x_8, x_344);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_unsigned_to_nat(0u);
x_353 = lean_box(0);
x_354 = lean_mk_string_unchecked("_private", 8, 8);
x_355 = l_Lean_Name_str___override(x_353, x_354);
lean_inc(x_10);
x_356 = l_Lean_Name_str___override(x_355, x_10);
x_357 = lean_mk_string_unchecked("DSL", 3, 3);
x_358 = l_Lean_Name_str___override(x_356, x_357);
x_359 = lean_mk_string_unchecked("VerLit", 6, 6);
x_360 = l_Lean_Name_str___override(x_358, x_359);
x_361 = l_Lean_Name_num___override(x_360, x_352);
x_362 = l_Lean_Name_str___override(x_361, x_10);
x_363 = lean_mk_string_unchecked("toResultExpr", 12, 12);
x_364 = l_Lean_Name_str___override(x_362, x_363);
x_365 = lean_mk_empty_array_with_capacity(x_306);
x_366 = lean_array_push(x_365, x_343);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_367 = l_Lean_Meta_mkAppM(x_364, x_366, x_5, x_6, x_7, x_8, x_351);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_370 = l_Lake_elabVerLit_unsafe__1(x_350, x_368, x_5, x_6, x_7, x_8, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(3, 1, 0);
} else {
 x_375 = x_374;
 lean_ctor_set_tag(x_375, 3);
}
lean_ctor_set(x_375, 0, x_373);
x_376 = l_Lean_MessageData_ofFormat(x_375);
x_377 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_376, x_3, x_4, x_5, x_6, x_7, x_8, x_372);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_378 = lean_ctor_get(x_370, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_379 = x_370;
} else {
 lean_dec_ref(x_370);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_371, 0);
lean_inc(x_380);
lean_dec(x_371);
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_382 = lean_ctor_get(x_370, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_370, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_384 = x_370;
} else {
 lean_dec_ref(x_370);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_dec(x_350);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_367;
}
}
else
{
lean_dec(x_343);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_349;
}
}
else
{
lean_dec(x_315);
lean_dec(x_296);
lean_dec(x_289);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_342;
}
}
else
{
lean_dec(x_296);
lean_dec(x_289);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_298;
}
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = !lean_is_exclusive(x_15);
if (x_386 == 0)
{
return x_15;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_15, 0);
x_388 = lean_ctor_get(x_15, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_15);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lake_elabVerLit__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
x_4 = lean_mk_string_unchecked("verLit", 6, 6);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("elabVerLit", 10, 10);
x_7 = l_Lean_Name_mkStr2(x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_Lake_elabVerLit), 9, 0);
x_9 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_5, x_7, x_8, x_1);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_VerLit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instToExprSemVerCore = _init_l_Lake_instToExprSemVerCore();
lean_mark_persistent(l_Lake_instToExprSemVerCore);
l_Lake_instToExprStdVer = _init_l_Lake_instToExprStdVer();
lean_mark_persistent(l_Lake_instToExprStdVer);
if (builtin) {res = l___regBuiltin_Lake_elabVerLit__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
