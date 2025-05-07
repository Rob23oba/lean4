// Lean compiler output
// Module: Lean.Util.SearchPath
// Imports: Lean.ToExpr Lean.Util.Path Lean.Elab.Term
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
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_termCompile__time__search__path_x25;
lean_object* l_Lean_logWarning___at___Lean_Linter_checkDeprecated___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_checkDeprecatedCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* _init_l_termCompile__time__search__path_x25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("termCompile_time_search_path%", 29, 29);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("compile_time_search_path%", 25, 25);
x_5 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("System", 6, 6);
x_7 = lean_mk_string_unchecked("FilePath", 8, 8);
x_8 = lean_mk_string_unchecked("mk", 2, 2);
x_9 = l_Lean_Name_mkStr3(x_6, x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
x_12 = l_Lean_mkStrLit(x_4);
x_13 = l_Lean_Expr_app___override(x_11, x_12);
lean_inc(x_2);
x_14 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(x_1, x_2, x_5);
x_15 = l_Lean_mkAppB(x_2, x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_string_unchecked("termCompile_time_search_path%", 29, 29);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_mk_string_unchecked("`compile_time_search_path%` is deprecated; use `initSearchPath (← findSysroot)` instead.", 90, 88);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = l_Lean_logWarning___at___Lean_Linter_checkDeprecated___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_checkDeprecatedCore_spec__0_spec__0(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_searchPathRef;
x_21 = lean_st_ref_get(x_20, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_mk_string_unchecked("System", 6, 6);
x_25 = lean_mk_string_unchecked("FilePath", 8, 8);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_29 = lean_mk_string_unchecked("List", 4, 4);
x_30 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_29);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
x_32 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_32);
lean_inc(x_16);
x_33 = l_Lean_Expr_const___override(x_31, x_16);
lean_inc(x_28);
x_34 = l_Lean_Expr_app___override(x_33, x_28);
x_35 = lean_mk_string_unchecked("cons", 4, 4);
x_36 = l_Lean_Name_mkStr2(x_29, x_35);
x_37 = l_Lean_Expr_const___override(x_36, x_16);
x_38 = l_Lean_Expr_app___override(x_37, x_28);
x_39 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(x_34, x_38, x_23);
lean_dec(x_34);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_mk_string_unchecked("System", 6, 6);
x_43 = lean_mk_string_unchecked("FilePath", 8, 8);
x_44 = l_Lean_Name_mkStr2(x_42, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_const___override(x_44, x_45);
x_47 = lean_mk_string_unchecked("List", 4, 4);
x_48 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_47);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_45);
lean_ctor_set(x_16, 0, x_50);
lean_inc(x_16);
x_51 = l_Lean_Expr_const___override(x_49, x_16);
lean_inc(x_46);
x_52 = l_Lean_Expr_app___override(x_51, x_46);
x_53 = lean_mk_string_unchecked("cons", 4, 4);
x_54 = l_Lean_Name_mkStr2(x_47, x_53);
x_55 = l_Lean_Expr_const___override(x_54, x_16);
x_56 = l_Lean_Expr_app___override(x_55, x_46);
x_57 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(x_52, x_56, x_40);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = l_Lean_searchPathRef;
x_61 = lean_st_ref_get(x_60, x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_mk_string_unchecked("System", 6, 6);
x_66 = lean_mk_string_unchecked("FilePath", 8, 8);
x_67 = l_Lean_Name_mkStr2(x_65, x_66);
x_68 = lean_box(0);
x_69 = l_Lean_Expr_const___override(x_67, x_68);
x_70 = lean_mk_string_unchecked("List", 4, 4);
x_71 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_70);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
lean_inc(x_74);
x_75 = l_Lean_Expr_const___override(x_72, x_74);
lean_inc(x_69);
x_76 = l_Lean_Expr_app___override(x_75, x_69);
x_77 = lean_mk_string_unchecked("cons", 4, 4);
x_78 = l_Lean_Name_mkStr2(x_70, x_77);
x_79 = l_Lean_Expr_const___override(x_78, x_74);
x_80 = l_Lean_Expr_app___override(x_79, x_69);
x_81 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(x_76, x_80, x_62);
lean_dec(x_76);
if (lean_is_scalar(x_64)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_64;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_63);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___aux__Lean__Util__SearchPath______elabRules__termCompile__time__search__path_x25__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SearchPath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_termCompile__time__search__path_x25 = _init_l_termCompile__time__search__path_x25();
lean_mark_persistent(l_termCompile__time__search__path_x25);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
