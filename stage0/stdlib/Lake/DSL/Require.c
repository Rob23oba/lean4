// Lean compiler output
// Module: Lake.DSL.Require
// Imports: Lean.Parser.Command Lake.Config.Dependency Lake.DSL.Extensions Lake.DSL.DeclUtil Lake.DSL.Syntax
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
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandRequireDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_expandRequireDecl__1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandRequireDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___lam__0(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_5);
x_6 = l_String_toSubstring_x27(x_5);
lean_inc(x_5);
x_7 = l_Lean_Name_mkStr1(x_5);
x_8 = l_Lean_addMacroScope(x_4, x_7, x_1);
x_9 = lean_mk_string_unchecked("Option", 6, 6);
x_10 = l_Lean_Name_mkStr2(x_9, x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_apply_2(x_3, lean_box(0), x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2), 5, 4);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("app", 3, 3);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_11);
x_12 = l_String_toSubstring_x27(x_11);
lean_inc(x_11);
x_13 = l_Lean_Name_mkStr1(x_11);
x_14 = l_Lean_addMacroScope(x_5, x_13, x_1);
x_15 = lean_mk_string_unchecked("Option", 6, 6);
x_16 = l_Lean_Name_mkStr2(x_15, x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_2);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_mk_string_unchecked("null", 4, 4);
x_23 = l_Lean_Name_mkStr1(x_22);
lean_inc(x_2);
x_24 = l_Lean_Syntax_node1(x_2, x_23, x_3);
x_25 = l_Lean_Syntax_node2(x_2, x_10, x_21, x_24);
x_26 = lean_apply_2(x_4, lean_box(0), x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5), 5, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4), 6, 5);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_4);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_3(x_6, lean_box(0), x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 4, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_5);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_16);
lean_inc(x_14);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6), 5, 4);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_14);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_inc(x_14);
lean_inc(x_20);
x_21 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_20, x_18);
lean_inc(x_14);
x_22 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_21, x_19);
x_23 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7___boxed), 4, 3);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_13);
lean_closure_set(x_23, 2, x_22);
x_24 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_20, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_6);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_6);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_17);
lean_inc(x_15);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6), 5, 4);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_15);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_inc(x_15);
lean_inc(x_21);
x_22 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_21, x_19);
lean_inc(x_15);
x_23 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_22, x_20);
x_24 = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7___boxed), 4, 3);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_23);
x_25 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_114; lean_object* x_179; uint8_t x_180; 
x_179 = l_Lean_Syntax_getArg(x_4, x_7);
x_180 = l_Lean_Syntax_isNone(x_179);
if (x_180 == 0)
{
uint8_t x_181; 
lean_inc(x_179);
x_181 = l_Lean_Syntax_matchesNull(x_179, x_8);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_183 = l_Lean_Macro_throwErrorAt(lean_box(0), x_9, x_182, x_13, x_14);
lean_dec(x_13);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_Lean_Syntax_getArg(x_179, x_10);
lean_dec(x_179);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_114 = x_185;
goto block_178;
}
}
else
{
lean_object* x_186; 
lean_dec(x_179);
x_186 = lean_box(0);
x_114 = x_186;
goto block_178;
}
block_48:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_SourceInfo_fromRef(x_17, x_22);
lean_dec(x_17);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Parser", 6, 6);
x_26 = lean_mk_string_unchecked("Term", 4, 4);
x_27 = lean_mk_string_unchecked("app", 3, 3);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_mk_string_unchecked("DependencySrc.git", 17, 17);
x_30 = l_String_toSubstring_x27(x_29);
x_31 = lean_mk_string_unchecked("DependencySrc", 13, 13);
x_32 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_32);
lean_inc(x_31);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = l_Lean_addMacroScope(x_18, x_33, x_16);
x_35 = l_Lean_Name_mkStr3(x_1, x_31, x_32);
x_36 = lean_box(0);
lean_inc(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_23);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_34);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_mk_string_unchecked("null", 4, 4);
x_44 = l_Lean_Name_mkStr1(x_43);
lean_inc(x_23);
x_45 = l_Lean_Syntax_node3(x_23, x_44, x_2, x_15, x_19);
x_46 = l_Lean_Syntax_node2(x_23, x_28, x_42, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_20);
return x_47;
}
block_113:
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_3);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
x_61 = l_Lean_SourceInfo_fromRef(x_54, x_60);
x_62 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_62);
x_63 = l_String_toSubstring_x27(x_62);
lean_inc(x_62);
x_64 = l_Lean_Name_mkStr1(x_62);
lean_inc(x_51);
lean_inc(x_55);
x_65 = l_Lean_addMacroScope(x_55, x_64, x_51);
x_66 = lean_mk_string_unchecked("Option", 6, 6);
x_67 = l_Lean_Name_mkStr2(x_66, x_62);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_65);
lean_ctor_set(x_72, 3, x_71);
x_15 = x_57;
x_16 = x_51;
x_17 = x_54;
x_18 = x_55;
x_19 = x_72;
x_20 = x_58;
goto block_48;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_52, 0);
lean_inc(x_73);
lean_dec(x_52);
lean_inc(x_3);
lean_inc(x_49);
x_74 = lean_apply_3(x_3, x_49, x_49, x_58);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_replaceRef(x_73, x_75);
lean_dec(x_75);
lean_inc(x_51);
lean_inc(x_55);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_56);
lean_ctor_set(x_78, 1, x_55);
lean_ctor_set(x_78, 2, x_51);
lean_ctor_set(x_78, 3, x_53);
lean_ctor_set(x_78, 4, x_50);
lean_ctor_set(x_78, 5, x_77);
lean_inc(x_78);
x_79 = lean_apply_3(x_3, x_78, x_78, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_SourceInfo_fromRef(x_80, x_83);
lean_dec(x_80);
x_85 = lean_mk_string_unchecked("Lean", 4, 4);
x_86 = lean_mk_string_unchecked("Parser", 6, 6);
x_87 = lean_mk_string_unchecked("Term", 4, 4);
x_88 = lean_mk_string_unchecked("app", 3, 3);
x_89 = l_Lean_Name_mkStr4(x_85, x_86, x_87, x_88);
x_90 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_90);
x_91 = l_String_toSubstring_x27(x_90);
lean_inc(x_90);
x_92 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_51);
lean_inc(x_55);
x_93 = l_Lean_addMacroScope(x_55, x_92, x_51);
x_94 = lean_mk_string_unchecked("Option", 6, 6);
x_95 = l_Lean_Name_mkStr2(x_94, x_90);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_84);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_84);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 2, x_93);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_mk_string_unchecked("null", 4, 4);
x_102 = l_Lean_Name_mkStr1(x_101);
lean_inc(x_84);
x_103 = l_Lean_Syntax_node1(x_84, x_102, x_73);
x_104 = l_Lean_Syntax_node2(x_84, x_89, x_100, x_103);
x_15 = x_57;
x_16 = x_51;
x_17 = x_54;
x_18 = x_55;
x_19 = x_104;
x_20 = x_81;
goto block_48;
}
else
{
uint8_t x_105; 
lean_dec(x_73);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_79);
if (x_105 == 0)
{
return x_79;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_79, 0);
x_107 = lean_ctor_get(x_79, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_79);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_73);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_74);
if (x_109 == 0)
{
return x_74;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_74, 0);
x_111 = lean_ctor_get(x_74, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_74);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_178:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = l_Lean_Syntax_getArg(x_4, x_5);
x_116 = lean_ctor_get(x_13, 5);
lean_inc(x_116);
x_117 = l_Lean_replaceRef(x_115, x_116);
lean_dec(x_116);
lean_dec(x_115);
x_118 = lean_ctor_get(x_13, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_13, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_13, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_13, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_13, 4);
lean_inc(x_122);
lean_dec(x_13);
lean_inc(x_117);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
x_123 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set(x_123, 2, x_120);
lean_ctor_set(x_123, 3, x_121);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set(x_123, 5, x_117);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_6);
x_124 = lean_box(0);
x_125 = lean_unbox(x_124);
x_126 = l_Lean_SourceInfo_fromRef(x_117, x_125);
x_127 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_127);
x_128 = l_String_toSubstring_x27(x_127);
lean_inc(x_127);
x_129 = l_Lean_Name_mkStr1(x_127);
lean_inc(x_120);
lean_inc(x_119);
x_130 = l_Lean_addMacroScope(x_119, x_129, x_120);
x_131 = lean_mk_string_unchecked("Option", 6, 6);
x_132 = l_Lean_Name_mkStr2(x_131, x_127);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_130);
lean_ctor_set(x_137, 3, x_136);
x_49 = x_123;
x_50 = x_122;
x_51 = x_120;
x_52 = x_114;
x_53 = x_121;
x_54 = x_117;
x_55 = x_119;
x_56 = x_118;
x_57 = x_137;
x_58 = x_14;
goto block_113;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_12, 0);
lean_inc(x_138);
lean_dec(x_12);
lean_inc(x_6);
lean_inc_n(x_123, 2);
x_139 = lean_apply_3(x_6, x_123, x_123, x_14);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_replaceRef(x_138, x_140);
lean_dec(x_140);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_118);
lean_ctor_set(x_143, 1, x_119);
lean_ctor_set(x_143, 2, x_120);
lean_ctor_set(x_143, 3, x_121);
lean_ctor_set(x_143, 4, x_122);
lean_ctor_set(x_143, 5, x_142);
lean_inc(x_143);
x_144 = lean_apply_3(x_6, x_143, x_143, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_box(0);
x_148 = lean_unbox(x_147);
x_149 = l_Lean_SourceInfo_fromRef(x_145, x_148);
lean_dec(x_145);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("Parser", 6, 6);
x_152 = lean_mk_string_unchecked("Term", 4, 4);
x_153 = lean_mk_string_unchecked("app", 3, 3);
x_154 = l_Lean_Name_mkStr4(x_150, x_151, x_152, x_153);
x_155 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_155);
x_156 = l_String_toSubstring_x27(x_155);
lean_inc(x_155);
x_157 = l_Lean_Name_mkStr1(x_155);
lean_inc(x_120);
lean_inc(x_119);
x_158 = l_Lean_addMacroScope(x_119, x_157, x_120);
x_159 = lean_mk_string_unchecked("Option", 6, 6);
x_160 = l_Lean_Name_mkStr2(x_159, x_155);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_149);
x_165 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_156);
lean_ctor_set(x_165, 2, x_158);
lean_ctor_set(x_165, 3, x_164);
x_166 = lean_mk_string_unchecked("null", 4, 4);
x_167 = l_Lean_Name_mkStr1(x_166);
lean_inc(x_149);
x_168 = l_Lean_Syntax_node1(x_149, x_167, x_138);
x_169 = l_Lean_Syntax_node2(x_149, x_154, x_165, x_168);
x_49 = x_123;
x_50 = x_122;
x_51 = x_120;
x_52 = x_114;
x_53 = x_121;
x_54 = x_117;
x_55 = x_119;
x_56 = x_118;
x_57 = x_169;
x_58 = x_146;
goto block_113;
}
else
{
uint8_t x_170; 
lean_dec(x_138);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_144);
if (x_170 == 0)
{
return x_144;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_144, 0);
x_172 = lean_ctor_get(x_144, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_144);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_138);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_139);
if (x_174 == 0)
{
return x_139;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_139, 0);
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_139);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_mk_string_unchecked("Lake", 4, 4);
x_135 = lean_mk_string_unchecked("DSL", 3, 3);
x_136 = lean_mk_string_unchecked("depSpec", 7, 7);
lean_inc(x_135);
lean_inc(x_134);
x_137 = l_Lean_Name_mkStr3(x_134, x_135, x_136);
lean_inc(x_1);
x_138 = l_Lean_Syntax_isOfKind(x_1, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_139 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_140 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_139, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_849; uint8_t x_850; 
x_141 = lean_alloc_closure((void*)(l_Lake_DSL_expandDepSpec___lam__0___boxed), 3, 0);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_Lean_Syntax_getArg(x_1, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_849 = l_Lean_Syntax_getArg(x_1, x_144);
x_850 = l_Lean_Syntax_isNone(x_849);
if (x_850 == 0)
{
uint8_t x_851; 
lean_inc(x_849);
x_851 = l_Lean_Syntax_matchesNull(x_849, x_144);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; 
lean_dec(x_849);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_852 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_853 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_852, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_853;
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; 
x_854 = l_Lean_Syntax_getArg(x_849, x_142);
lean_dec(x_849);
x_855 = lean_mk_string_unchecked("verClause", 9, 9);
lean_inc(x_135);
lean_inc(x_134);
x_856 = l_Lean_Name_mkStr3(x_134, x_135, x_855);
lean_inc(x_854);
x_857 = l_Lean_Syntax_isOfKind(x_854, x_856);
lean_dec(x_856);
if (x_857 == 0)
{
lean_object* x_858; lean_object* x_859; 
lean_dec(x_854);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_858 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_859 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_858, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_859;
}
else
{
lean_object* x_860; lean_object* x_861; 
x_860 = l_Lean_Syntax_getArg(x_854, x_144);
lean_dec(x_854);
x_861 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_861, 0, x_860);
x_830 = x_861;
x_831 = x_3;
x_832 = x_4;
goto block_848;
}
}
}
else
{
lean_object* x_862; 
lean_dec(x_849);
x_862 = lean_box(0);
x_830 = x_862;
x_831 = x_3;
x_832 = x_4;
goto block_848;
}
block_258:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_inc(x_164);
x_171 = l_Array_append(lean_box(0), x_164, x_170);
lean_dec(x_170);
lean_inc(x_157);
lean_inc(x_149);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_149);
lean_ctor_set(x_172, 1, x_157);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_174 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_173);
x_175 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_149);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_149);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_178 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_177);
x_179 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_180 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_179);
lean_inc(x_157);
lean_inc(x_149);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_149);
lean_ctor_set(x_181, 1, x_157);
lean_ctor_set(x_181, 2, x_164);
lean_inc(x_181);
lean_inc(x_149);
x_182 = l_Lean_Syntax_node1(x_149, x_180, x_181);
x_183 = lean_mk_string_unchecked("Attr", 4, 4);
x_184 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_145);
lean_inc(x_169);
x_185 = l_Lean_Name_mkStr4(x_169, x_145, x_183, x_184);
x_186 = lean_mk_string_unchecked("package_dep", 11, 11);
lean_inc(x_186);
x_187 = l_String_toSubstring_x27(x_186);
x_188 = l_Lean_Name_mkStr1(x_186);
lean_inc(x_156);
lean_inc(x_166);
x_189 = l_Lean_addMacroScope(x_166, x_188, x_156);
x_190 = lean_box(0);
lean_inc(x_149);
x_191 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_191, 0, x_149);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_189);
lean_ctor_set(x_191, 3, x_190);
lean_inc(x_181);
lean_inc(x_149);
x_192 = l_Lean_Syntax_node2(x_149, x_185, x_191, x_181);
lean_inc(x_149);
x_193 = l_Lean_Syntax_node2(x_149, x_178, x_182, x_192);
lean_inc(x_157);
lean_inc(x_149);
x_194 = l_Lean_Syntax_node1(x_149, x_157, x_193);
x_195 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_149);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_149);
lean_ctor_set(x_196, 1, x_195);
lean_inc(x_149);
x_197 = l_Lean_Syntax_node3(x_149, x_174, x_176, x_194, x_196);
lean_inc(x_157);
lean_inc(x_149);
x_198 = l_Lean_Syntax_node1(x_149, x_157, x_197);
lean_inc_n(x_181, 4);
lean_inc(x_149);
x_199 = l_Lean_Syntax_node6(x_149, x_160, x_172, x_198, x_181, x_181, x_181, x_181);
x_200 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_154);
lean_inc(x_145);
lean_inc(x_169);
x_201 = l_Lean_Name_mkStr4(x_169, x_145, x_154, x_200);
x_202 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_149);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_149);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_154);
lean_inc(x_145);
lean_inc(x_169);
x_205 = l_Lean_Name_mkStr4(x_169, x_145, x_154, x_204);
x_206 = l_Lake_DSL_expandIdentOrStrAsIdent(x_163);
x_207 = lean_mk_empty_array_with_capacity(x_142);
x_208 = lean_box(2);
lean_inc(x_157);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_157);
lean_ctor_set(x_209, 2, x_207);
x_210 = lean_mk_empty_array_with_capacity(x_159);
x_211 = lean_array_push(x_210, x_206);
x_212 = lean_array_push(x_211, x_209);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_205);
lean_ctor_set(x_213, 2, x_212);
x_214 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_154);
lean_inc(x_145);
lean_inc(x_169);
x_215 = l_Lean_Name_mkStr4(x_169, x_145, x_154, x_214);
x_216 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_217 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_216);
x_218 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_149);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_149);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_mk_string_unchecked("Dependency", 10, 10);
x_221 = l_Lean_Name_mkStr2(x_134, x_220);
x_222 = l_Lean_mkCIdent(x_221);
lean_inc(x_149);
x_223 = l_Lean_Syntax_node2(x_149, x_217, x_219, x_222);
lean_inc(x_157);
lean_inc(x_149);
x_224 = l_Lean_Syntax_node1(x_149, x_157, x_223);
lean_inc(x_181);
lean_inc(x_149);
x_225 = l_Lean_Syntax_node2(x_149, x_215, x_181, x_224);
x_226 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_145);
lean_inc(x_169);
x_227 = l_Lean_Name_mkStr4(x_169, x_145, x_154, x_226);
x_228 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_149);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_149);
lean_ctor_set(x_229, 1, x_228);
lean_inc(x_149);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_149);
lean_ctor_set(x_230, 1, x_162);
x_231 = lean_mk_string_unchecked("structInstField", 15, 15);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_232 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_231);
x_233 = lean_mk_string_unchecked("structInstLVal", 14, 14);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_234 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_233);
x_235 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_235);
x_236 = l_String_toSubstring_x27(x_235);
x_237 = l_Lean_Name_mkStr1(x_235);
lean_inc(x_156);
lean_inc(x_166);
x_238 = l_Lean_addMacroScope(x_166, x_237, x_156);
lean_inc(x_149);
x_239 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_239, 0, x_149);
lean_ctor_set(x_239, 1, x_236);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_190);
lean_inc(x_181);
lean_inc(x_234);
lean_inc(x_149);
x_240 = l_Lean_Syntax_node2(x_149, x_234, x_239, x_181);
x_241 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
lean_inc(x_152);
lean_inc(x_145);
lean_inc(x_169);
x_242 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_241);
x_243 = l_Lean_Syntax_getId(x_151);
lean_dec(x_151);
x_244 = lean_box(0);
lean_inc(x_243);
x_245 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_244, x_243);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
lean_dec(x_152);
x_246 = l_Lean_quoteNameMk(x_243);
x_62 = x_146;
x_63 = x_145;
x_64 = x_225;
x_65 = x_147;
x_66 = x_148;
x_67 = x_230;
x_68 = x_149;
x_69 = x_190;
x_70 = x_150;
x_71 = x_232;
x_72 = x_203;
x_73 = x_229;
x_74 = x_181;
x_75 = x_240;
x_76 = x_153;
x_77 = x_155;
x_78 = x_156;
x_79 = x_234;
x_80 = x_157;
x_81 = x_242;
x_82 = x_201;
x_83 = x_158;
x_84 = x_213;
x_85 = x_227;
x_86 = x_161;
x_87 = x_165;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_199;
x_93 = x_246;
goto block_133;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_243);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_145);
lean_inc(x_169);
x_249 = l_Lean_Name_mkStr4(x_169, x_145, x_152, x_248);
x_250 = lean_mk_string_unchecked("`", 1, 1);
x_251 = lean_mk_string_unchecked(".", 1, 1);
x_252 = l_String_intercalate(x_251, x_247);
lean_dec(x_251);
x_253 = lean_string_append(x_250, x_252);
lean_dec(x_252);
x_254 = l_Lean_Syntax_mkNameLit(x_253, x_208);
x_255 = lean_mk_empty_array_with_capacity(x_144);
x_256 = lean_array_push(x_255, x_254);
x_257 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_257, 0, x_208);
lean_ctor_set(x_257, 1, x_249);
lean_ctor_set(x_257, 2, x_256);
x_62 = x_146;
x_63 = x_145;
x_64 = x_225;
x_65 = x_147;
x_66 = x_148;
x_67 = x_230;
x_68 = x_149;
x_69 = x_190;
x_70 = x_150;
x_71 = x_232;
x_72 = x_203;
x_73 = x_229;
x_74 = x_181;
x_75 = x_240;
x_76 = x_153;
x_77 = x_155;
x_78 = x_156;
x_79 = x_234;
x_80 = x_157;
x_81 = x_242;
x_82 = x_201;
x_83 = x_158;
x_84 = x_213;
x_85 = x_227;
x_86 = x_161;
x_87 = x_165;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_199;
x_93 = x_257;
goto block_133;
}
}
block_400:
{
lean_object* x_268; uint8_t x_269; 
x_268 = l_Lake_DSL_expandDepSpec___lam__0(x_261, x_261, x_267);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
x_272 = lean_mk_string_unchecked("term{}", 6, 6);
x_273 = lean_mk_string_unchecked("null", 4, 4);
x_274 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_275 = lean_mk_string_unchecked("optEllipsis", 11, 11);
x_276 = l_Lake_DSL_expandDepSpec___lam__0(x_261, x_261, x_271);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
x_280 = lean_box(0);
x_281 = lean_unbox(x_280);
x_282 = l_Lean_SourceInfo_fromRef(x_270, x_281);
lean_dec(x_270);
x_283 = lean_mk_string_unchecked("choice", 6, 6);
x_284 = l_Lean_Name_mkStr1(x_272);
x_285 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_285);
lean_inc(x_282);
lean_ctor_set_tag(x_276, 2);
lean_ctor_set(x_276, 1, x_285);
lean_ctor_set(x_276, 0, x_282);
x_286 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_286);
lean_inc(x_282);
lean_ctor_set_tag(x_268, 2);
lean_ctor_set(x_268, 1, x_286);
lean_ctor_set(x_268, 0, x_282);
x_287 = lean_mk_string_unchecked("Lean", 4, 4);
x_288 = lean_mk_string_unchecked("Parser", 6, 6);
x_289 = lean_mk_string_unchecked("Term", 4, 4);
x_290 = lean_mk_string_unchecked("structInst", 10, 10);
x_291 = l_Lean_Name_mkStr1(x_273);
x_292 = l_Array_mkArray0(lean_box(0));
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_282);
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_282);
lean_ctor_set(x_293, 1, x_291);
lean_ctor_set(x_293, 2, x_292);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
x_294 = l_Lean_Name_mkStr4(x_287, x_288, x_289, x_274);
lean_inc(x_293);
lean_inc(x_294);
lean_inc(x_282);
x_295 = l_Lean_Syntax_node1(x_282, x_294, x_293);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
x_296 = l_Lean_Name_mkStr4(x_287, x_288, x_289, x_275);
lean_inc(x_293);
lean_inc(x_296);
lean_inc(x_282);
x_297 = l_Lean_Syntax_node1(x_282, x_296, x_293);
x_298 = l_Lean_Name_mkStr1(x_283);
lean_inc(x_268);
lean_inc(x_276);
lean_inc(x_282);
x_299 = l_Lean_Syntax_node2(x_282, x_284, x_276, x_268);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
x_300 = l_Lean_Name_mkStr4(x_287, x_288, x_289, x_290);
lean_inc(x_293);
lean_inc(x_300);
lean_inc(x_282);
x_301 = l_Lean_Syntax_node6(x_282, x_300, x_276, x_293, x_295, x_297, x_293, x_268);
x_302 = l_Lean_Syntax_node2(x_282, x_298, x_299, x_301);
x_303 = lean_unbox(x_280);
x_304 = l_Lean_SourceInfo_fromRef(x_278, x_303);
lean_dec(x_278);
x_305 = lean_ctor_get(x_261, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_261, 1);
lean_inc(x_306);
lean_dec(x_261);
x_307 = lean_mk_string_unchecked("Command", 7, 7);
x_308 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_307);
lean_inc(x_288);
lean_inc(x_287);
x_309 = l_Lean_Name_mkStr4(x_287, x_288, x_307, x_308);
x_310 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_307);
lean_inc(x_288);
lean_inc(x_287);
x_311 = l_Lean_Name_mkStr4(x_287, x_288, x_307, x_310);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_312; 
x_312 = l_Array_empty(lean_box(0));
x_145 = x_288;
x_146 = x_279;
x_147 = x_260;
x_148 = x_263;
x_149 = x_304;
x_150 = x_262;
x_151 = x_264;
x_152 = x_289;
x_153 = x_294;
x_154 = x_307;
x_155 = x_302;
x_156 = x_305;
x_157 = x_291;
x_158 = x_266;
x_159 = x_265;
x_160 = x_311;
x_161 = x_296;
x_162 = x_285;
x_163 = x_259;
x_164 = x_292;
x_165 = x_300;
x_166 = x_306;
x_167 = x_309;
x_168 = x_286;
x_169 = x_287;
x_170 = x_312;
goto block_258;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_2, 0);
lean_inc(x_313);
lean_dec(x_2);
x_314 = l_Array_mkArray1___redArg(x_313);
x_145 = x_288;
x_146 = x_279;
x_147 = x_260;
x_148 = x_263;
x_149 = x_304;
x_150 = x_262;
x_151 = x_264;
x_152 = x_289;
x_153 = x_294;
x_154 = x_307;
x_155 = x_302;
x_156 = x_305;
x_157 = x_291;
x_158 = x_266;
x_159 = x_265;
x_160 = x_311;
x_161 = x_296;
x_162 = x_285;
x_163 = x_259;
x_164 = x_292;
x_165 = x_300;
x_166 = x_306;
x_167 = x_309;
x_168 = x_286;
x_169 = x_287;
x_170 = x_314;
goto block_258;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_315 = lean_ctor_get(x_276, 0);
x_316 = lean_ctor_get(x_276, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_276);
x_317 = lean_box(0);
x_318 = lean_unbox(x_317);
x_319 = l_Lean_SourceInfo_fromRef(x_270, x_318);
lean_dec(x_270);
x_320 = lean_mk_string_unchecked("choice", 6, 6);
x_321 = l_Lean_Name_mkStr1(x_272);
x_322 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_322);
lean_inc(x_319);
x_323 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_324);
lean_inc(x_319);
lean_ctor_set_tag(x_268, 2);
lean_ctor_set(x_268, 1, x_324);
lean_ctor_set(x_268, 0, x_319);
x_325 = lean_mk_string_unchecked("Lean", 4, 4);
x_326 = lean_mk_string_unchecked("Parser", 6, 6);
x_327 = lean_mk_string_unchecked("Term", 4, 4);
x_328 = lean_mk_string_unchecked("structInst", 10, 10);
x_329 = l_Lean_Name_mkStr1(x_273);
x_330 = l_Array_mkArray0(lean_box(0));
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_319);
x_331 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_331, 0, x_319);
lean_ctor_set(x_331, 1, x_329);
lean_ctor_set(x_331, 2, x_330);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
x_332 = l_Lean_Name_mkStr4(x_325, x_326, x_327, x_274);
lean_inc(x_331);
lean_inc(x_332);
lean_inc(x_319);
x_333 = l_Lean_Syntax_node1(x_319, x_332, x_331);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
x_334 = l_Lean_Name_mkStr4(x_325, x_326, x_327, x_275);
lean_inc(x_331);
lean_inc(x_334);
lean_inc(x_319);
x_335 = l_Lean_Syntax_node1(x_319, x_334, x_331);
x_336 = l_Lean_Name_mkStr1(x_320);
lean_inc(x_268);
lean_inc(x_323);
lean_inc(x_319);
x_337 = l_Lean_Syntax_node2(x_319, x_321, x_323, x_268);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
x_338 = l_Lean_Name_mkStr4(x_325, x_326, x_327, x_328);
lean_inc(x_331);
lean_inc(x_338);
lean_inc(x_319);
x_339 = l_Lean_Syntax_node6(x_319, x_338, x_323, x_331, x_333, x_335, x_331, x_268);
x_340 = l_Lean_Syntax_node2(x_319, x_336, x_337, x_339);
x_341 = lean_unbox(x_317);
x_342 = l_Lean_SourceInfo_fromRef(x_315, x_341);
lean_dec(x_315);
x_343 = lean_ctor_get(x_261, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_261, 1);
lean_inc(x_344);
lean_dec(x_261);
x_345 = lean_mk_string_unchecked("Command", 7, 7);
x_346 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_345);
lean_inc(x_326);
lean_inc(x_325);
x_347 = l_Lean_Name_mkStr4(x_325, x_326, x_345, x_346);
x_348 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_345);
lean_inc(x_326);
lean_inc(x_325);
x_349 = l_Lean_Name_mkStr4(x_325, x_326, x_345, x_348);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_350; 
x_350 = l_Array_empty(lean_box(0));
x_145 = x_326;
x_146 = x_316;
x_147 = x_260;
x_148 = x_263;
x_149 = x_342;
x_150 = x_262;
x_151 = x_264;
x_152 = x_327;
x_153 = x_332;
x_154 = x_345;
x_155 = x_340;
x_156 = x_343;
x_157 = x_329;
x_158 = x_266;
x_159 = x_265;
x_160 = x_349;
x_161 = x_334;
x_162 = x_322;
x_163 = x_259;
x_164 = x_330;
x_165 = x_338;
x_166 = x_344;
x_167 = x_347;
x_168 = x_324;
x_169 = x_325;
x_170 = x_350;
goto block_258;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_2, 0);
lean_inc(x_351);
lean_dec(x_2);
x_352 = l_Array_mkArray1___redArg(x_351);
x_145 = x_326;
x_146 = x_316;
x_147 = x_260;
x_148 = x_263;
x_149 = x_342;
x_150 = x_262;
x_151 = x_264;
x_152 = x_327;
x_153 = x_332;
x_154 = x_345;
x_155 = x_340;
x_156 = x_343;
x_157 = x_329;
x_158 = x_266;
x_159 = x_265;
x_160 = x_349;
x_161 = x_334;
x_162 = x_322;
x_163 = x_259;
x_164 = x_330;
x_165 = x_338;
x_166 = x_344;
x_167 = x_347;
x_168 = x_324;
x_169 = x_325;
x_170 = x_352;
goto block_258;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_353 = lean_ctor_get(x_268, 0);
x_354 = lean_ctor_get(x_268, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_268);
x_355 = lean_mk_string_unchecked("term{}", 6, 6);
x_356 = lean_mk_string_unchecked("null", 4, 4);
x_357 = lean_mk_string_unchecked("structInstFields", 16, 16);
x_358 = lean_mk_string_unchecked("optEllipsis", 11, 11);
x_359 = l_Lake_DSL_expandDepSpec___lam__0(x_261, x_261, x_354);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = lean_box(0);
x_364 = lean_unbox(x_363);
x_365 = l_Lean_SourceInfo_fromRef(x_353, x_364);
lean_dec(x_353);
x_366 = lean_mk_string_unchecked("choice", 6, 6);
x_367 = l_Lean_Name_mkStr1(x_355);
x_368 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_368);
lean_inc(x_365);
if (lean_is_scalar(x_362)) {
 x_369 = lean_alloc_ctor(2, 2, 0);
} else {
 x_369 = x_362;
 lean_ctor_set_tag(x_369, 2);
}
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_370);
lean_inc(x_365);
x_371 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_371, 0, x_365);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_mk_string_unchecked("Lean", 4, 4);
x_373 = lean_mk_string_unchecked("Parser", 6, 6);
x_374 = lean_mk_string_unchecked("Term", 4, 4);
x_375 = lean_mk_string_unchecked("structInst", 10, 10);
x_376 = l_Lean_Name_mkStr1(x_356);
x_377 = l_Array_mkArray0(lean_box(0));
lean_inc(x_377);
lean_inc(x_376);
lean_inc(x_365);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_365);
lean_ctor_set(x_378, 1, x_376);
lean_ctor_set(x_378, 2, x_377);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
x_379 = l_Lean_Name_mkStr4(x_372, x_373, x_374, x_357);
lean_inc(x_378);
lean_inc(x_379);
lean_inc(x_365);
x_380 = l_Lean_Syntax_node1(x_365, x_379, x_378);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
x_381 = l_Lean_Name_mkStr4(x_372, x_373, x_374, x_358);
lean_inc(x_378);
lean_inc(x_381);
lean_inc(x_365);
x_382 = l_Lean_Syntax_node1(x_365, x_381, x_378);
x_383 = l_Lean_Name_mkStr1(x_366);
lean_inc(x_371);
lean_inc(x_369);
lean_inc(x_365);
x_384 = l_Lean_Syntax_node2(x_365, x_367, x_369, x_371);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
x_385 = l_Lean_Name_mkStr4(x_372, x_373, x_374, x_375);
lean_inc(x_378);
lean_inc(x_385);
lean_inc(x_365);
x_386 = l_Lean_Syntax_node6(x_365, x_385, x_369, x_378, x_380, x_382, x_378, x_371);
x_387 = l_Lean_Syntax_node2(x_365, x_383, x_384, x_386);
x_388 = lean_unbox(x_363);
x_389 = l_Lean_SourceInfo_fromRef(x_360, x_388);
lean_dec(x_360);
x_390 = lean_ctor_get(x_261, 2);
lean_inc(x_390);
x_391 = lean_ctor_get(x_261, 1);
lean_inc(x_391);
lean_dec(x_261);
x_392 = lean_mk_string_unchecked("Command", 7, 7);
x_393 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_392);
lean_inc(x_373);
lean_inc(x_372);
x_394 = l_Lean_Name_mkStr4(x_372, x_373, x_392, x_393);
x_395 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_392);
lean_inc(x_373);
lean_inc(x_372);
x_396 = l_Lean_Name_mkStr4(x_372, x_373, x_392, x_395);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_397; 
x_397 = l_Array_empty(lean_box(0));
x_145 = x_373;
x_146 = x_361;
x_147 = x_260;
x_148 = x_263;
x_149 = x_389;
x_150 = x_262;
x_151 = x_264;
x_152 = x_374;
x_153 = x_379;
x_154 = x_392;
x_155 = x_387;
x_156 = x_390;
x_157 = x_376;
x_158 = x_266;
x_159 = x_265;
x_160 = x_396;
x_161 = x_381;
x_162 = x_368;
x_163 = x_259;
x_164 = x_377;
x_165 = x_385;
x_166 = x_391;
x_167 = x_394;
x_168 = x_370;
x_169 = x_372;
x_170 = x_397;
goto block_258;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_2, 0);
lean_inc(x_398);
lean_dec(x_2);
x_399 = l_Array_mkArray1___redArg(x_398);
x_145 = x_373;
x_146 = x_361;
x_147 = x_260;
x_148 = x_263;
x_149 = x_389;
x_150 = x_262;
x_151 = x_264;
x_152 = x_374;
x_153 = x_379;
x_154 = x_392;
x_155 = x_387;
x_156 = x_390;
x_157 = x_376;
x_158 = x_266;
x_159 = x_265;
x_160 = x_396;
x_161 = x_381;
x_162 = x_368;
x_163 = x_259;
x_164 = x_377;
x_165 = x_385;
x_166 = x_391;
x_167 = x_394;
x_168 = x_370;
x_169 = x_372;
x_170 = x_399;
goto block_258;
}
}
}
block_524:
{
lean_object* x_409; 
lean_inc(x_402);
x_409 = l_Lake_DSL_expandIdentOrStrAsIdent(x_402);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_410 = lean_ctor_get(x_407, 5);
lean_inc(x_410);
x_411 = lean_box(0);
x_412 = lean_unbox(x_411);
x_413 = l_Lean_SourceInfo_fromRef(x_410, x_412);
lean_dec(x_410);
x_414 = lean_ctor_get(x_407, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_407, 1);
lean_inc(x_415);
x_416 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_416);
x_417 = l_String_toSubstring_x27(x_416);
lean_inc(x_416);
x_418 = l_Lean_Name_mkStr1(x_416);
x_419 = l_Lean_addMacroScope(x_415, x_418, x_414);
x_420 = lean_mk_string_unchecked("Option", 6, 6);
x_421 = l_Lean_Name_mkStr2(x_420, x_416);
x_422 = lean_box(0);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_426, 0, x_413);
lean_ctor_set(x_426, 1, x_417);
lean_ctor_set(x_426, 2, x_419);
lean_ctor_set(x_426, 3, x_425);
x_259 = x_402;
x_260 = x_401;
x_261 = x_407;
x_262 = x_403;
x_263 = x_406;
x_264 = x_409;
x_265 = x_404;
x_266 = x_426;
x_267 = x_408;
goto block_400;
}
else
{
lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_427 = lean_ctor_get(x_405, 0);
lean_inc(x_427);
lean_dec(x_405);
x_428 = l_Lake_DSL_expandDepSpec___lam__0(x_407, x_407, x_408);
x_429 = !lean_is_exclusive(x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_430 = lean_ctor_get(x_428, 0);
x_431 = lean_ctor_get(x_428, 1);
x_432 = l_Lean_replaceRef(x_427, x_430);
lean_dec(x_430);
x_433 = lean_ctor_get(x_407, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_407, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_407, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_407, 3);
lean_inc(x_436);
x_437 = lean_ctor_get(x_407, 4);
lean_inc(x_437);
lean_inc(x_435);
lean_inc(x_434);
x_438 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_438, 0, x_433);
lean_ctor_set(x_438, 1, x_434);
lean_ctor_set(x_438, 2, x_435);
lean_ctor_set(x_438, 3, x_436);
lean_ctor_set(x_438, 4, x_437);
lean_ctor_set(x_438, 5, x_432);
x_439 = l_Lake_DSL_expandDepSpec___lam__0(x_438, x_438, x_431);
lean_dec(x_438);
x_440 = !lean_is_exclusive(x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_441 = lean_ctor_get(x_439, 0);
x_442 = lean_ctor_get(x_439, 1);
x_443 = lean_box(0);
x_444 = lean_unbox(x_443);
x_445 = l_Lean_SourceInfo_fromRef(x_441, x_444);
lean_dec(x_441);
x_446 = lean_mk_string_unchecked("Lean", 4, 4);
x_447 = lean_mk_string_unchecked("Parser", 6, 6);
x_448 = lean_mk_string_unchecked("Term", 4, 4);
x_449 = lean_mk_string_unchecked("app", 3, 3);
x_450 = l_Lean_Name_mkStr4(x_446, x_447, x_448, x_449);
x_451 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_451);
x_452 = l_String_toSubstring_x27(x_451);
lean_inc(x_451);
x_453 = l_Lean_Name_mkStr1(x_451);
x_454 = l_Lean_addMacroScope(x_434, x_453, x_435);
x_455 = lean_mk_string_unchecked("Option", 6, 6);
x_456 = l_Lean_Name_mkStr2(x_455, x_451);
x_457 = lean_box(0);
lean_ctor_set_tag(x_439, 1);
lean_ctor_set(x_439, 1, x_457);
lean_ctor_set(x_439, 0, x_456);
x_458 = lean_box(0);
lean_ctor_set_tag(x_428, 1);
lean_ctor_set(x_428, 1, x_458);
lean_ctor_set(x_428, 0, x_439);
lean_inc(x_445);
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_445);
lean_ctor_set(x_459, 1, x_452);
lean_ctor_set(x_459, 2, x_454);
lean_ctor_set(x_459, 3, x_428);
x_460 = lean_mk_string_unchecked("null", 4, 4);
x_461 = l_Lean_Name_mkStr1(x_460);
lean_inc(x_445);
x_462 = l_Lean_Syntax_node1(x_445, x_461, x_427);
x_463 = l_Lean_Syntax_node2(x_445, x_450, x_459, x_462);
x_259 = x_402;
x_260 = x_401;
x_261 = x_407;
x_262 = x_403;
x_263 = x_406;
x_264 = x_409;
x_265 = x_404;
x_266 = x_463;
x_267 = x_442;
goto block_400;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_464 = lean_ctor_get(x_439, 0);
x_465 = lean_ctor_get(x_439, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_439);
x_466 = lean_box(0);
x_467 = lean_unbox(x_466);
x_468 = l_Lean_SourceInfo_fromRef(x_464, x_467);
lean_dec(x_464);
x_469 = lean_mk_string_unchecked("Lean", 4, 4);
x_470 = lean_mk_string_unchecked("Parser", 6, 6);
x_471 = lean_mk_string_unchecked("Term", 4, 4);
x_472 = lean_mk_string_unchecked("app", 3, 3);
x_473 = l_Lean_Name_mkStr4(x_469, x_470, x_471, x_472);
x_474 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_474);
x_475 = l_String_toSubstring_x27(x_474);
lean_inc(x_474);
x_476 = l_Lean_Name_mkStr1(x_474);
x_477 = l_Lean_addMacroScope(x_434, x_476, x_435);
x_478 = lean_mk_string_unchecked("Option", 6, 6);
x_479 = l_Lean_Name_mkStr2(x_478, x_474);
x_480 = lean_box(0);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
x_482 = lean_box(0);
lean_ctor_set_tag(x_428, 1);
lean_ctor_set(x_428, 1, x_482);
lean_ctor_set(x_428, 0, x_481);
lean_inc(x_468);
x_483 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_483, 0, x_468);
lean_ctor_set(x_483, 1, x_475);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_428);
x_484 = lean_mk_string_unchecked("null", 4, 4);
x_485 = l_Lean_Name_mkStr1(x_484);
lean_inc(x_468);
x_486 = l_Lean_Syntax_node1(x_468, x_485, x_427);
x_487 = l_Lean_Syntax_node2(x_468, x_473, x_483, x_486);
x_259 = x_402;
x_260 = x_401;
x_261 = x_407;
x_262 = x_403;
x_263 = x_406;
x_264 = x_409;
x_265 = x_404;
x_266 = x_487;
x_267 = x_465;
goto block_400;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_488 = lean_ctor_get(x_428, 0);
x_489 = lean_ctor_get(x_428, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_428);
x_490 = l_Lean_replaceRef(x_427, x_488);
lean_dec(x_488);
x_491 = lean_ctor_get(x_407, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_407, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_407, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_407, 3);
lean_inc(x_494);
x_495 = lean_ctor_get(x_407, 4);
lean_inc(x_495);
lean_inc(x_493);
lean_inc(x_492);
x_496 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_496, 0, x_491);
lean_ctor_set(x_496, 1, x_492);
lean_ctor_set(x_496, 2, x_493);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set(x_496, 4, x_495);
lean_ctor_set(x_496, 5, x_490);
x_497 = l_Lake_DSL_expandDepSpec___lam__0(x_496, x_496, x_489);
lean_dec(x_496);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_500 = x_497;
} else {
 lean_dec_ref(x_497);
 x_500 = lean_box(0);
}
x_501 = lean_box(0);
x_502 = lean_unbox(x_501);
x_503 = l_Lean_SourceInfo_fromRef(x_498, x_502);
lean_dec(x_498);
x_504 = lean_mk_string_unchecked("Lean", 4, 4);
x_505 = lean_mk_string_unchecked("Parser", 6, 6);
x_506 = lean_mk_string_unchecked("Term", 4, 4);
x_507 = lean_mk_string_unchecked("app", 3, 3);
x_508 = l_Lean_Name_mkStr4(x_504, x_505, x_506, x_507);
x_509 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_509);
x_510 = l_String_toSubstring_x27(x_509);
lean_inc(x_509);
x_511 = l_Lean_Name_mkStr1(x_509);
x_512 = l_Lean_addMacroScope(x_492, x_511, x_493);
x_513 = lean_mk_string_unchecked("Option", 6, 6);
x_514 = l_Lean_Name_mkStr2(x_513, x_509);
x_515 = lean_box(0);
if (lean_is_scalar(x_500)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_500;
 lean_ctor_set_tag(x_516, 1);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_box(0);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
lean_inc(x_503);
x_519 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_519, 0, x_503);
lean_ctor_set(x_519, 1, x_510);
lean_ctor_set(x_519, 2, x_512);
lean_ctor_set(x_519, 3, x_518);
x_520 = lean_mk_string_unchecked("null", 4, 4);
x_521 = l_Lean_Name_mkStr1(x_520);
lean_inc(x_503);
x_522 = l_Lean_Syntax_node1(x_503, x_521, x_427);
x_523 = l_Lean_Syntax_node2(x_503, x_508, x_519, x_522);
x_259 = x_402;
x_260 = x_401;
x_261 = x_407;
x_262 = x_403;
x_263 = x_406;
x_264 = x_409;
x_265 = x_404;
x_266 = x_523;
x_267 = x_499;
goto block_400;
}
}
}
block_612:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_534 = lean_ctor_get(x_529, 5);
lean_inc(x_534);
x_535 = l_Lean_replaceRef(x_527, x_534);
lean_dec(x_534);
x_536 = lean_ctor_get(x_529, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_529, 1);
lean_inc(x_537);
x_538 = lean_ctor_get(x_529, 2);
lean_inc(x_538);
x_539 = lean_ctor_get(x_529, 3);
lean_inc(x_539);
x_540 = lean_ctor_get(x_529, 4);
lean_inc(x_540);
lean_inc(x_535);
lean_inc(x_538);
lean_inc(x_537);
x_541 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_541, 0, x_536);
lean_ctor_set(x_541, 1, x_537);
lean_ctor_set(x_541, 2, x_538);
lean_ctor_set(x_541, 3, x_539);
lean_ctor_set(x_541, 4, x_540);
lean_ctor_set(x_541, 5, x_535);
if (x_533 == 0)
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_134);
lean_dec(x_2);
x_542 = lean_mk_string_unchecked("ill-formed version syntax", 25, 25);
x_543 = l_Lean_Macro_throwErrorAt(lean_box(0), x_527, x_542, x_541, x_532);
lean_dec(x_541);
lean_dec(x_527);
return x_543;
}
else
{
lean_object* x_544; uint8_t x_545; 
x_544 = l_Lean_Syntax_getArg(x_527, x_142);
lean_inc(x_544);
x_545 = l_Lean_Syntax_matchesNull(x_544, x_144);
if (x_545 == 0)
{
uint8_t x_546; 
x_546 = l_Lean_Syntax_matchesNull(x_544, x_142);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_134);
lean_dec(x_2);
x_547 = lean_mk_string_unchecked("ill-formed version syntax", 25, 25);
x_548 = l_Lean_Macro_throwErrorAt(lean_box(0), x_527, x_547, x_541, x_532);
lean_dec(x_541);
lean_dec(x_527);
return x_548;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_541);
x_549 = l_Lean_Syntax_getArg(x_527, x_144);
lean_dec(x_527);
x_550 = l_Lean_SourceInfo_fromRef(x_535, x_545);
lean_dec(x_535);
x_551 = lean_mk_string_unchecked("Lean", 4, 4);
x_552 = lean_mk_string_unchecked("Parser", 6, 6);
x_553 = lean_mk_string_unchecked("Term", 4, 4);
x_554 = lean_mk_string_unchecked("app", 3, 3);
x_555 = l_Lean_Name_mkStr4(x_551, x_552, x_553, x_554);
x_556 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_556);
x_557 = l_String_toSubstring_x27(x_556);
lean_inc(x_556);
x_558 = l_Lean_Name_mkStr1(x_556);
x_559 = l_Lean_addMacroScope(x_537, x_558, x_538);
x_560 = lean_mk_string_unchecked("Option", 6, 6);
x_561 = l_Lean_Name_mkStr2(x_560, x_556);
x_562 = lean_box(0);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_box(0);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
lean_inc(x_550);
x_566 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_566, 0, x_550);
lean_ctor_set(x_566, 1, x_557);
lean_ctor_set(x_566, 2, x_559);
lean_ctor_set(x_566, 3, x_565);
x_567 = lean_mk_string_unchecked("null", 4, 4);
x_568 = l_Lean_Name_mkStr1(x_567);
lean_inc(x_550);
x_569 = l_Lean_Syntax_node1(x_550, x_568, x_549);
x_570 = l_Lean_Syntax_node2(x_550, x_555, x_566, x_569);
x_401 = x_525;
x_402 = x_526;
x_403 = x_528;
x_404 = x_530;
x_405 = x_531;
x_406 = x_570;
x_407 = x_529;
x_408 = x_532;
goto block_524;
}
}
else
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_544);
lean_dec(x_541);
x_571 = l_Lean_Syntax_getArg(x_527, x_144);
lean_dec(x_527);
x_572 = lean_box(0);
x_573 = lean_unbox(x_572);
x_574 = l_Lean_SourceInfo_fromRef(x_535, x_573);
lean_dec(x_535);
x_575 = lean_mk_string_unchecked("Lean", 4, 4);
x_576 = lean_mk_string_unchecked("Parser", 6, 6);
x_577 = lean_mk_string_unchecked("Term", 4, 4);
x_578 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
x_579 = l_Lean_Name_mkStr4(x_575, x_576, x_577, x_578);
x_580 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_580);
x_581 = l_String_toSubstring_x27(x_580);
lean_inc(x_580);
x_582 = l_Lean_Name_mkStr1(x_580);
x_583 = l_Lean_addMacroScope(x_537, x_582, x_538);
x_584 = lean_mk_string_unchecked("Option", 6, 6);
x_585 = l_Lean_Name_mkStr2(x_584, x_580);
x_586 = lean_box(0);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_box(0);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
lean_inc(x_574);
x_590 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_590, 0, x_574);
lean_ctor_set(x_590, 1, x_581);
lean_ctor_set(x_590, 2, x_583);
lean_ctor_set(x_590, 3, x_589);
x_591 = lean_mk_string_unchecked("null", 4, 4);
x_592 = l_Lean_Name_mkStr1(x_591);
x_593 = lean_mk_string_unchecked("paren", 5, 5);
x_594 = l_Lean_Name_mkStr4(x_575, x_576, x_577, x_593);
x_595 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_574);
x_596 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_596, 0, x_574);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_mk_string_unchecked("term_++_", 8, 8);
x_598 = l_Lean_Name_mkStr1(x_597);
x_599 = lean_mk_string_unchecked("str", 3, 3);
x_600 = l_Lean_Name_mkStr1(x_599);
x_601 = lean_mk_string_unchecked("\"git#\"", 6, 6);
lean_inc(x_574);
x_602 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_602, 0, x_574);
lean_ctor_set(x_602, 1, x_601);
lean_inc(x_574);
x_603 = l_Lean_Syntax_node1(x_574, x_600, x_602);
x_604 = lean_mk_string_unchecked("++", 2, 2);
lean_inc(x_574);
x_605 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_605, 0, x_574);
lean_ctor_set(x_605, 1, x_604);
lean_inc(x_574);
x_606 = l_Lean_Syntax_node3(x_574, x_598, x_603, x_605, x_571);
x_607 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_574);
x_608 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_608, 0, x_574);
lean_ctor_set(x_608, 1, x_607);
lean_inc(x_574);
x_609 = l_Lean_Syntax_node3(x_574, x_594, x_596, x_606, x_608);
lean_inc(x_574);
x_610 = l_Lean_Syntax_node1(x_574, x_592, x_609);
x_611 = l_Lean_Syntax_node2(x_574, x_579, x_590, x_610);
x_401 = x_525;
x_402 = x_526;
x_403 = x_528;
x_404 = x_530;
x_405 = x_531;
x_406 = x_611;
x_407 = x_529;
x_408 = x_532;
goto block_524;
}
}
}
block_642:
{
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
lean_dec(x_135);
x_621 = lean_ctor_get(x_616, 5);
lean_inc(x_621);
x_622 = lean_box(0);
x_623 = lean_unbox(x_622);
x_624 = l_Lean_SourceInfo_fromRef(x_621, x_623);
lean_dec(x_621);
x_625 = lean_ctor_get(x_616, 2);
lean_inc(x_625);
x_626 = lean_ctor_get(x_616, 1);
lean_inc(x_626);
x_627 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_627);
x_628 = l_String_toSubstring_x27(x_627);
lean_inc(x_627);
x_629 = l_Lean_Name_mkStr1(x_627);
x_630 = l_Lean_addMacroScope(x_626, x_629, x_625);
x_631 = lean_mk_string_unchecked("Option", 6, 6);
x_632 = l_Lean_Name_mkStr2(x_631, x_627);
x_633 = lean_box(0);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
x_635 = lean_box(0);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
x_637 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_637, 0, x_624);
lean_ctor_set(x_637, 1, x_628);
lean_ctor_set(x_637, 2, x_630);
lean_ctor_set(x_637, 3, x_636);
x_401 = x_620;
x_402 = x_613;
x_403 = x_615;
x_404 = x_617;
x_405 = x_619;
x_406 = x_637;
x_407 = x_616;
x_408 = x_618;
goto block_524;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
x_638 = lean_ctor_get(x_614, 0);
lean_inc(x_638);
lean_dec(x_614);
x_639 = lean_mk_string_unchecked("verSpec", 7, 7);
lean_inc(x_134);
x_640 = l_Lean_Name_mkStr3(x_134, x_135, x_639);
lean_inc(x_638);
x_641 = l_Lean_Syntax_isOfKind(x_638, x_640);
lean_dec(x_640);
if (x_641 == 0)
{
x_525 = x_620;
x_526 = x_613;
x_527 = x_638;
x_528 = x_615;
x_529 = x_616;
x_530 = x_617;
x_531 = x_619;
x_532 = x_618;
x_533 = x_641;
goto block_612;
}
else
{
x_525 = x_620;
x_526 = x_613;
x_527 = x_638;
x_528 = x_615;
x_529 = x_616;
x_530 = x_617;
x_531 = x_619;
x_532 = x_618;
x_533 = x_138;
goto block_612;
}
}
}
block_666:
{
uint8_t x_650; 
lean_inc(x_143);
x_650 = l_Lean_Syntax_isOfKind(x_143, x_643);
lean_dec(x_643);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_648);
lean_dec(x_645);
lean_dec(x_644);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_651 = lean_mk_string_unchecked("ill-formed name syntax", 22, 22);
x_652 = l_Lean_Macro_throwErrorAt(lean_box(0), x_143, x_651, x_647, x_649);
lean_dec(x_647);
lean_dec(x_143);
return x_652;
}
else
{
lean_object* x_653; uint8_t x_654; 
x_653 = l_Lean_Syntax_getArg(x_143, x_142);
x_654 = l_Lean_Syntax_isNone(x_653);
if (x_654 == 0)
{
uint8_t x_655; 
lean_inc(x_653);
x_655 = l_Lean_Syntax_matchesNull(x_653, x_646);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_653);
lean_dec(x_648);
lean_dec(x_645);
lean_dec(x_644);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_656 = lean_mk_string_unchecked("ill-formed name syntax", 22, 22);
x_657 = l_Lean_Macro_throwErrorAt(lean_box(0), x_143, x_656, x_647, x_649);
lean_dec(x_647);
lean_dec(x_143);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; 
x_658 = l_Lean_Syntax_getArg(x_653, x_142);
lean_dec(x_653);
x_659 = l_Lean_Syntax_getArg(x_143, x_144);
lean_dec(x_143);
x_613 = x_659;
x_614 = x_644;
x_615 = x_645;
x_616 = x_647;
x_617 = x_646;
x_618 = x_649;
x_619 = x_648;
x_620 = x_658;
goto block_642;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_653);
x_660 = l_Lean_Syntax_getArg(x_143, x_144);
x_661 = lean_mk_string_unchecked("", 0, 0);
x_662 = lean_box(0);
x_663 = lean_unbox(x_662);
x_664 = l_Lean_SourceInfo_fromRef(x_143, x_663);
lean_dec(x_143);
x_665 = l_Lean_Syntax_mkStrLit(x_661, x_664);
lean_dec(x_661);
x_613 = x_660;
x_614 = x_644;
x_615 = x_645;
x_616 = x_647;
x_617 = x_646;
x_618 = x_649;
x_619 = x_648;
x_620 = x_665;
goto block_642;
}
}
}
block_675:
{
lean_object* x_674; 
x_674 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_674, 0, x_672);
x_643 = x_667;
x_644 = x_668;
x_645 = x_669;
x_646 = x_670;
x_647 = x_671;
x_648 = x_674;
x_649 = x_673;
goto block_666;
}
block_684:
{
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_667 = x_676;
x_668 = x_677;
x_669 = x_678;
x_670 = x_679;
x_671 = x_680;
x_672 = x_682;
x_673 = x_683;
goto block_675;
}
else
{
lean_dec(x_680);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_676);
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
return x_681;
}
}
block_808:
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_mk_string_unchecked("depName", 7, 7);
lean_inc(x_135);
lean_inc(x_134);
x_693 = l_Lean_Name_mkStr3(x_134, x_135, x_692);
if (lean_obj_tag(x_687) == 0)
{
lean_dec(x_141);
x_643 = x_693;
x_644 = x_688;
x_645 = x_691;
x_646 = x_690;
x_647 = x_685;
x_648 = x_687;
x_649 = x_689;
goto block_666;
}
else
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_687);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
x_695 = lean_ctor_get(x_687, 0);
x_696 = lean_mk_string_unchecked("fromSource", 10, 10);
lean_inc(x_135);
lean_inc(x_134);
x_697 = l_Lean_Name_mkStr3(x_134, x_135, x_696);
lean_inc(x_695);
x_698 = l_Lean_Syntax_isOfKind(x_695, x_697);
lean_dec(x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
lean_free_object(x_687);
lean_dec(x_141);
x_699 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_700 = l_Lean_Macro_throwErrorAt(lean_box(0), x_695, x_699, x_685, x_689);
lean_dec(x_695);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_700;
goto block_684;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_701 = l_Lean_Syntax_getArg(x_695, x_142);
x_702 = lean_mk_string_unchecked("fromGit", 7, 7);
lean_inc(x_135);
lean_inc(x_134);
x_703 = l_Lean_Name_mkStr3(x_134, x_135, x_702);
lean_inc(x_701);
x_704 = l_Lean_Syntax_isOfKind(x_701, x_703);
lean_dec(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_free_object(x_687);
lean_dec(x_141);
x_705 = lean_mk_string_unchecked("fromPath", 8, 8);
lean_inc(x_135);
lean_inc(x_134);
x_706 = l_Lean_Name_mkStr3(x_134, x_135, x_705);
lean_inc(x_701);
x_707 = l_Lean_Syntax_isOfKind(x_701, x_706);
lean_dec(x_706);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_701);
x_708 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_709 = l_Lean_Macro_throwErrorAt(lean_box(0), x_695, x_708, x_685, x_689);
lean_dec(x_695);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_709;
goto block_684;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_710 = l_Lean_Syntax_getArg(x_701, x_142);
lean_dec(x_701);
x_711 = lean_ctor_get(x_685, 5);
lean_inc(x_711);
x_712 = l_Lean_replaceRef(x_695, x_711);
lean_dec(x_711);
lean_dec(x_695);
x_713 = lean_ctor_get(x_685, 1);
lean_inc(x_713);
x_714 = lean_ctor_get(x_685, 2);
lean_inc(x_714);
x_715 = l_Lean_SourceInfo_fromRef(x_712, x_704);
lean_dec(x_712);
x_716 = lean_mk_string_unchecked("Lean", 4, 4);
x_717 = lean_mk_string_unchecked("Parser", 6, 6);
x_718 = lean_mk_string_unchecked("Term", 4, 4);
x_719 = lean_mk_string_unchecked("app", 3, 3);
x_720 = l_Lean_Name_mkStr4(x_716, x_717, x_718, x_719);
x_721 = lean_mk_string_unchecked("DependencySrc.path", 18, 18);
x_722 = l_String_toSubstring_x27(x_721);
x_723 = lean_mk_string_unchecked("DependencySrc", 13, 13);
x_724 = lean_mk_string_unchecked("path", 4, 4);
lean_inc(x_724);
lean_inc(x_723);
x_725 = l_Lean_Name_mkStr2(x_723, x_724);
x_726 = l_Lean_addMacroScope(x_713, x_725, x_714);
lean_inc(x_134);
x_727 = l_Lean_Name_mkStr3(x_134, x_723, x_724);
x_728 = lean_box(0);
lean_inc(x_727);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_730, 0, x_727);
x_731 = lean_box(0);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_729);
lean_ctor_set(x_733, 1, x_732);
lean_inc(x_715);
x_734 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_734, 0, x_715);
lean_ctor_set(x_734, 1, x_722);
lean_ctor_set(x_734, 2, x_726);
lean_ctor_set(x_734, 3, x_733);
x_735 = lean_mk_string_unchecked("null", 4, 4);
x_736 = l_Lean_Name_mkStr1(x_735);
lean_inc(x_715);
x_737 = l_Lean_Syntax_node1(x_715, x_736, x_710);
x_738 = l_Lean_Syntax_node2(x_715, x_720, x_734, x_737);
x_667 = x_693;
x_668 = x_688;
x_669 = x_691;
x_670 = x_690;
x_671 = x_685;
x_672 = x_738;
x_673 = x_689;
goto block_675;
}
}
else
{
lean_object* x_739; lean_object* x_740; uint8_t x_741; 
x_739 = l_Lean_Syntax_getArg(x_701, x_144);
x_740 = l_Lean_Syntax_getArg(x_701, x_690);
x_741 = l_Lean_Syntax_isNone(x_740);
if (x_741 == 0)
{
uint8_t x_742; 
lean_inc(x_740);
x_742 = l_Lean_Syntax_matchesNull(x_740, x_690);
if (x_742 == 0)
{
lean_object* x_743; lean_object* x_744; 
lean_dec(x_740);
lean_dec(x_739);
lean_dec(x_701);
lean_free_object(x_687);
lean_dec(x_141);
x_743 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_744 = l_Lean_Macro_throwErrorAt(lean_box(0), x_695, x_743, x_685, x_689);
lean_dec(x_695);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_744;
goto block_684;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = l_Lean_Syntax_getArg(x_740, x_144);
lean_dec(x_740);
x_746 = lean_box(0);
lean_ctor_set(x_687, 0, x_745);
lean_inc(x_685);
lean_inc(x_141);
lean_inc(x_134);
x_747 = l_Lake_DSL_expandDepSpec___lam__4(x_134, x_739, x_141, x_701, x_142, x_141, x_686, x_690, x_695, x_144, x_746, x_687, x_685, x_689);
lean_dec(x_695);
lean_dec(x_701);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_747;
goto block_684;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_740);
lean_free_object(x_687);
x_748 = lean_box(0);
x_749 = lean_box(0);
lean_inc(x_685);
lean_inc(x_141);
lean_inc(x_134);
x_750 = l_Lake_DSL_expandDepSpec___lam__4(x_134, x_739, x_141, x_701, x_142, x_141, x_686, x_690, x_695, x_144, x_748, x_749, x_685, x_689);
lean_dec(x_695);
lean_dec(x_701);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_750;
goto block_684;
}
}
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; 
x_751 = lean_ctor_get(x_687, 0);
lean_inc(x_751);
lean_dec(x_687);
x_752 = lean_mk_string_unchecked("fromSource", 10, 10);
lean_inc(x_135);
lean_inc(x_134);
x_753 = l_Lean_Name_mkStr3(x_134, x_135, x_752);
lean_inc(x_751);
x_754 = l_Lean_Syntax_isOfKind(x_751, x_753);
lean_dec(x_753);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_141);
x_755 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_756 = l_Lean_Macro_throwErrorAt(lean_box(0), x_751, x_755, x_685, x_689);
lean_dec(x_751);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_756;
goto block_684;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; 
x_757 = l_Lean_Syntax_getArg(x_751, x_142);
x_758 = lean_mk_string_unchecked("fromGit", 7, 7);
lean_inc(x_135);
lean_inc(x_134);
x_759 = l_Lean_Name_mkStr3(x_134, x_135, x_758);
lean_inc(x_757);
x_760 = l_Lean_Syntax_isOfKind(x_757, x_759);
lean_dec(x_759);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; uint8_t x_763; 
lean_dec(x_141);
x_761 = lean_mk_string_unchecked("fromPath", 8, 8);
lean_inc(x_135);
lean_inc(x_134);
x_762 = l_Lean_Name_mkStr3(x_134, x_135, x_761);
lean_inc(x_757);
x_763 = l_Lean_Syntax_isOfKind(x_757, x_762);
lean_dec(x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; 
lean_dec(x_757);
x_764 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_765 = l_Lean_Macro_throwErrorAt(lean_box(0), x_751, x_764, x_685, x_689);
lean_dec(x_751);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_765;
goto block_684;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_766 = l_Lean_Syntax_getArg(x_757, x_142);
lean_dec(x_757);
x_767 = lean_ctor_get(x_685, 5);
lean_inc(x_767);
x_768 = l_Lean_replaceRef(x_751, x_767);
lean_dec(x_767);
lean_dec(x_751);
x_769 = lean_ctor_get(x_685, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_685, 2);
lean_inc(x_770);
x_771 = l_Lean_SourceInfo_fromRef(x_768, x_760);
lean_dec(x_768);
x_772 = lean_mk_string_unchecked("Lean", 4, 4);
x_773 = lean_mk_string_unchecked("Parser", 6, 6);
x_774 = lean_mk_string_unchecked("Term", 4, 4);
x_775 = lean_mk_string_unchecked("app", 3, 3);
x_776 = l_Lean_Name_mkStr4(x_772, x_773, x_774, x_775);
x_777 = lean_mk_string_unchecked("DependencySrc.path", 18, 18);
x_778 = l_String_toSubstring_x27(x_777);
x_779 = lean_mk_string_unchecked("DependencySrc", 13, 13);
x_780 = lean_mk_string_unchecked("path", 4, 4);
lean_inc(x_780);
lean_inc(x_779);
x_781 = l_Lean_Name_mkStr2(x_779, x_780);
x_782 = l_Lean_addMacroScope(x_769, x_781, x_770);
lean_inc(x_134);
x_783 = l_Lean_Name_mkStr3(x_134, x_779, x_780);
x_784 = lean_box(0);
lean_inc(x_783);
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
x_786 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_786, 0, x_783);
x_787 = lean_box(0);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_789, 0, x_785);
lean_ctor_set(x_789, 1, x_788);
lean_inc(x_771);
x_790 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_790, 0, x_771);
lean_ctor_set(x_790, 1, x_778);
lean_ctor_set(x_790, 2, x_782);
lean_ctor_set(x_790, 3, x_789);
x_791 = lean_mk_string_unchecked("null", 4, 4);
x_792 = l_Lean_Name_mkStr1(x_791);
lean_inc(x_771);
x_793 = l_Lean_Syntax_node1(x_771, x_792, x_766);
x_794 = l_Lean_Syntax_node2(x_771, x_776, x_790, x_793);
x_667 = x_693;
x_668 = x_688;
x_669 = x_691;
x_670 = x_690;
x_671 = x_685;
x_672 = x_794;
x_673 = x_689;
goto block_675;
}
}
else
{
lean_object* x_795; lean_object* x_796; uint8_t x_797; 
x_795 = l_Lean_Syntax_getArg(x_757, x_144);
x_796 = l_Lean_Syntax_getArg(x_757, x_690);
x_797 = l_Lean_Syntax_isNone(x_796);
if (x_797 == 0)
{
uint8_t x_798; 
lean_inc(x_796);
x_798 = l_Lean_Syntax_matchesNull(x_796, x_690);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; 
lean_dec(x_796);
lean_dec(x_795);
lean_dec(x_757);
lean_dec(x_141);
x_799 = lean_mk_string_unchecked("ill-formed from syntax", 22, 22);
x_800 = l_Lean_Macro_throwErrorAt(lean_box(0), x_751, x_799, x_685, x_689);
lean_dec(x_751);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_800;
goto block_684;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_801 = l_Lean_Syntax_getArg(x_796, x_144);
lean_dec(x_796);
x_802 = lean_box(0);
x_803 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_803, 0, x_801);
lean_inc(x_685);
lean_inc(x_141);
lean_inc(x_134);
x_804 = l_Lake_DSL_expandDepSpec___lam__4(x_134, x_795, x_141, x_757, x_142, x_141, x_686, x_690, x_751, x_144, x_802, x_803, x_685, x_689);
lean_dec(x_751);
lean_dec(x_757);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_804;
goto block_684;
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_796);
x_805 = lean_box(0);
x_806 = lean_box(0);
lean_inc(x_685);
lean_inc(x_141);
lean_inc(x_134);
x_807 = l_Lake_DSL_expandDepSpec___lam__4(x_134, x_795, x_141, x_757, x_142, x_141, x_686, x_690, x_751, x_144, x_805, x_806, x_685, x_689);
lean_dec(x_751);
lean_dec(x_757);
x_676 = x_693;
x_677 = x_688;
x_678 = x_691;
x_679 = x_690;
x_680 = x_685;
x_681 = x_807;
goto block_684;
}
}
}
}
}
}
block_829:
{
lean_object* x_814; lean_object* x_815; uint8_t x_816; 
x_814 = lean_unsigned_to_nat(3u);
x_815 = l_Lean_Syntax_getArg(x_1, x_814);
x_816 = l_Lean_Syntax_isNone(x_815);
if (x_816 == 0)
{
uint8_t x_817; 
lean_inc(x_815);
x_817 = l_Lean_Syntax_matchesNull(x_815, x_144);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; 
lean_dec(x_815);
lean_dec(x_813);
lean_dec(x_810);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_818 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_819 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_818, x_809, x_811);
lean_dec(x_809);
lean_dec(x_1);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_820 = l_Lean_Syntax_getArg(x_815, x_142);
lean_dec(x_815);
x_821 = lean_mk_string_unchecked("withClause", 10, 10);
lean_inc(x_135);
lean_inc(x_134);
x_822 = l_Lean_Name_mkStr3(x_134, x_135, x_821);
lean_inc(x_820);
x_823 = l_Lean_Syntax_isOfKind(x_820, x_822);
lean_dec(x_822);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; 
lean_dec(x_820);
lean_dec(x_813);
lean_dec(x_810);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_824 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_825 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_824, x_809, x_811);
lean_dec(x_809);
lean_dec(x_1);
return x_825;
}
else
{
lean_object* x_826; lean_object* x_827; 
lean_dec(x_1);
x_826 = l_Lean_Syntax_getArg(x_820, x_144);
lean_dec(x_820);
x_827 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_827, 0, x_826);
x_685 = x_809;
x_686 = x_814;
x_687 = x_813;
x_688 = x_810;
x_689 = x_811;
x_690 = x_812;
x_691 = x_827;
goto block_808;
}
}
}
else
{
lean_object* x_828; 
lean_dec(x_815);
lean_dec(x_1);
x_828 = lean_box(0);
x_685 = x_809;
x_686 = x_814;
x_687 = x_813;
x_688 = x_810;
x_689 = x_811;
x_690 = x_812;
x_691 = x_828;
goto block_808;
}
}
block_848:
{
lean_object* x_833; lean_object* x_834; uint8_t x_835; 
x_833 = lean_unsigned_to_nat(2u);
x_834 = l_Lean_Syntax_getArg(x_1, x_833);
x_835 = l_Lean_Syntax_isNone(x_834);
if (x_835 == 0)
{
uint8_t x_836; 
lean_inc(x_834);
x_836 = l_Lean_Syntax_matchesNull(x_834, x_144);
if (x_836 == 0)
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_834);
lean_dec(x_830);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_837 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_838 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_837, x_831, x_832);
lean_dec(x_831);
lean_dec(x_1);
return x_838;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_839 = l_Lean_Syntax_getArg(x_834, x_142);
lean_dec(x_834);
x_840 = lean_mk_string_unchecked("fromClause", 10, 10);
lean_inc(x_135);
lean_inc(x_134);
x_841 = l_Lean_Name_mkStr3(x_134, x_135, x_840);
lean_inc(x_839);
x_842 = l_Lean_Syntax_isOfKind(x_839, x_841);
lean_dec(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; 
lean_dec(x_839);
lean_dec(x_830);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
x_843 = lean_mk_string_unchecked("ill-formed require syntax", 25, 25);
x_844 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_843, x_831, x_832);
lean_dec(x_831);
lean_dec(x_1);
return x_844;
}
else
{
lean_object* x_845; lean_object* x_846; 
x_845 = l_Lean_Syntax_getArg(x_839, x_144);
lean_dec(x_839);
x_846 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_846, 0, x_845);
x_809 = x_831;
x_810 = x_830;
x_811 = x_832;
x_812 = x_833;
x_813 = x_846;
goto block_829;
}
}
}
else
{
lean_object* x_847; 
lean_dec(x_834);
x_847 = lean_box(0);
x_809 = x_831;
x_810 = x_830;
x_811 = x_832;
x_812 = x_833;
x_813 = x_847;
goto block_829;
}
}
}
block_61:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_13);
lean_inc(x_9);
x_33 = l_Lean_Syntax_node2(x_9, x_18, x_13, x_32);
lean_inc_n(x_14, 2);
lean_inc(x_17);
lean_inc(x_9);
x_34 = l_Lean_Syntax_node3(x_9, x_17, x_14, x_14, x_33);
lean_inc(x_9);
x_35 = l_Lean_Syntax_node2(x_9, x_10, x_23, x_34);
x_36 = lean_unsigned_to_nat(10u);
x_37 = lean_mk_empty_array_with_capacity(x_36);
x_38 = lean_array_push(x_37, x_25);
lean_inc(x_31);
x_39 = lean_array_push(x_38, x_31);
x_40 = lean_array_push(x_39, x_26);
lean_inc(x_31);
x_41 = lean_array_push(x_40, x_31);
x_42 = lean_array_push(x_41, x_16);
lean_inc(x_31);
x_43 = lean_array_push(x_42, x_31);
x_44 = lean_array_push(x_43, x_12);
lean_inc(x_31);
x_45 = lean_array_push(x_44, x_31);
x_46 = lean_array_push(x_45, x_35);
x_47 = lean_array_push(x_46, x_31);
lean_inc(x_9);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_17);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_9);
x_49 = l_Lean_Syntax_node1(x_9, x_15, x_48);
lean_inc(x_14);
lean_inc(x_9);
x_50 = l_Lean_Syntax_node1(x_9, x_22, x_14);
lean_inc(x_9);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_27);
lean_inc_n(x_14, 2);
lean_inc(x_9);
x_52 = l_Lean_Syntax_node6(x_9, x_24, x_8, x_14, x_49, x_50, x_14, x_51);
x_53 = lean_mk_string_unchecked("Termination", 11, 11);
x_54 = lean_mk_string_unchecked("suffix", 6, 6);
x_55 = l_Lean_Name_mkStr4(x_30, x_6, x_53, x_54);
lean_inc_n(x_14, 2);
lean_inc(x_9);
x_56 = l_Lean_Syntax_node2(x_9, x_55, x_14, x_14);
lean_inc(x_14);
lean_inc(x_9);
x_57 = l_Lean_Syntax_node4(x_9, x_21, x_13, x_52, x_56, x_14);
lean_inc(x_9);
x_58 = l_Lean_Syntax_node5(x_9, x_19, x_11, x_20, x_7, x_57, x_14);
x_59 = l_Lean_Syntax_node2(x_9, x_28, x_29, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
return x_60;
}
block_133:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_73);
lean_inc(x_81);
lean_inc(x_68);
x_94 = l_Lean_Syntax_node2(x_68, x_81, x_73, x_93);
lean_inc_n(x_74, 2);
lean_inc(x_80);
lean_inc(x_68);
x_95 = l_Lean_Syntax_node3(x_68, x_80, x_74, x_74, x_94);
lean_inc(x_71);
lean_inc(x_68);
x_96 = l_Lean_Syntax_node2(x_68, x_71, x_75, x_95);
x_97 = lean_mk_string_unchecked(",", 1, 1);
lean_inc(x_68);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_68);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("scope", 5, 5);
lean_inc(x_99);
x_100 = l_String_toSubstring_x27(x_99);
x_101 = l_Lean_Name_mkStr1(x_99);
lean_inc(x_78);
lean_inc(x_88);
x_102 = l_Lean_addMacroScope(x_88, x_101, x_78);
lean_inc(x_69);
lean_inc(x_68);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_68);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_69);
lean_inc(x_74);
lean_inc(x_79);
lean_inc(x_68);
x_104 = l_Lean_Syntax_node2(x_68, x_79, x_103, x_74);
lean_inc(x_73);
lean_inc(x_81);
lean_inc(x_68);
x_105 = l_Lean_Syntax_node2(x_68, x_81, x_73, x_65);
lean_inc_n(x_74, 2);
lean_inc(x_80);
lean_inc(x_68);
x_106 = l_Lean_Syntax_node3(x_68, x_80, x_74, x_74, x_105);
lean_inc(x_71);
lean_inc(x_68);
x_107 = l_Lean_Syntax_node2(x_68, x_71, x_104, x_106);
x_108 = lean_mk_string_unchecked("version\?", 8, 8);
lean_inc(x_108);
x_109 = l_String_toSubstring_x27(x_108);
x_110 = l_Lean_Name_mkStr1(x_108);
lean_inc(x_78);
lean_inc(x_88);
x_111 = l_Lean_addMacroScope(x_88, x_110, x_78);
lean_inc(x_69);
lean_inc(x_68);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_68);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_69);
lean_inc(x_74);
lean_inc(x_79);
lean_inc(x_68);
x_113 = l_Lean_Syntax_node2(x_68, x_79, x_112, x_74);
lean_inc(x_73);
lean_inc(x_81);
lean_inc(x_68);
x_114 = l_Lean_Syntax_node2(x_68, x_81, x_73, x_66);
lean_inc_n(x_74, 2);
lean_inc(x_80);
lean_inc(x_68);
x_115 = l_Lean_Syntax_node3(x_68, x_80, x_74, x_74, x_114);
lean_inc(x_71);
lean_inc(x_68);
x_116 = l_Lean_Syntax_node2(x_68, x_71, x_113, x_115);
x_117 = lean_mk_string_unchecked("src\?", 4, 4);
lean_inc(x_117);
x_118 = l_String_toSubstring_x27(x_117);
x_119 = l_Lean_Name_mkStr1(x_117);
lean_inc(x_78);
lean_inc(x_88);
x_120 = l_Lean_addMacroScope(x_88, x_119, x_78);
lean_inc(x_69);
lean_inc(x_68);
x_121 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_121, 0, x_68);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_120);
lean_ctor_set(x_121, 3, x_69);
lean_inc(x_74);
lean_inc(x_79);
lean_inc(x_68);
x_122 = l_Lean_Syntax_node2(x_68, x_79, x_121, x_74);
lean_inc(x_73);
lean_inc(x_81);
lean_inc(x_68);
x_123 = l_Lean_Syntax_node2(x_68, x_81, x_73, x_83);
lean_inc_n(x_74, 2);
lean_inc(x_80);
lean_inc(x_68);
x_124 = l_Lean_Syntax_node3(x_68, x_80, x_74, x_74, x_123);
lean_inc(x_71);
lean_inc(x_68);
x_125 = l_Lean_Syntax_node2(x_68, x_71, x_122, x_124);
x_126 = lean_mk_string_unchecked("opts", 4, 4);
lean_inc(x_126);
x_127 = l_String_toSubstring_x27(x_126);
x_128 = l_Lean_Name_mkStr1(x_126);
x_129 = l_Lean_addMacroScope(x_88, x_128, x_78);
lean_inc(x_68);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_68);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_69);
lean_inc(x_74);
lean_inc(x_68);
x_131 = l_Lean_Syntax_node2(x_68, x_79, x_130, x_74);
if (lean_obj_tag(x_70) == 0)
{
x_5 = x_62;
x_6 = x_63;
x_7 = x_64;
x_8 = x_67;
x_9 = x_68;
x_10 = x_71;
x_11 = x_72;
x_12 = x_125;
x_13 = x_73;
x_14 = x_74;
x_15 = x_76;
x_16 = x_116;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_84;
x_21 = x_85;
x_22 = x_86;
x_23 = x_131;
x_24 = x_87;
x_25 = x_96;
x_26 = x_107;
x_27 = x_90;
x_28 = x_89;
x_29 = x_92;
x_30 = x_91;
x_31 = x_98;
x_32 = x_77;
goto block_61;
}
else
{
lean_object* x_132; 
lean_dec(x_77);
x_132 = lean_ctor_get(x_70, 0);
lean_inc(x_132);
lean_dec(x_70);
x_5 = x_62;
x_6 = x_63;
x_7 = x_64;
x_8 = x_67;
x_9 = x_68;
x_10 = x_71;
x_11 = x_72;
x_12 = x_125;
x_13 = x_73;
x_14 = x_74;
x_15 = x_76;
x_16 = x_116;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_84;
x_21 = x_85;
x_22 = x_86;
x_23 = x_131;
x_24 = x_87;
x_25 = x_96;
x_26 = x_107;
x_27 = x_90;
x_28 = x_89;
x_29 = x_92;
x_30 = x_91;
x_31 = x_98;
x_32 = x_132;
goto block_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL_expandDepSpec___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_DSL_expandDepSpec___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandRequireDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_5 = lean_mk_string_unchecked("DSL", 3, 3);
x_6 = lean_mk_string_unchecked("requireDecl", 11, 11);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_mk_string_unchecked("ill-formed require declaration", 30, 30);
x_10 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_9, x_2, x_3);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_36; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_36 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_17 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
x_17 = x_36;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_17 = x_40;
goto block_35;
}
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 5);
x_19 = l_Lean_replaceRef(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_19);
x_26 = l_Lake_DSL_expandDepSpec(x_15, x_17, x_25, x_3);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandRequireDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL_expandRequireDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_expandRequireDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
x_4 = lean_mk_string_unchecked("DSL", 3, 3);
x_5 = lean_mk_string_unchecked("requireDecl", 11, 11);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("expandRequireDecl", 17, 17);
x_8 = l_Lean_Name_mkStr3(x_3, x_4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_DSL_expandRequireDecl___boxed), 3, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_8, x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_instCoeRequireDeclCommand() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_DSL_instCoeRequireDeclCommand___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_DSL_instCoeRequireDeclCommand___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Require(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lake_DSL_expandRequireDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lake_DSL_instCoeRequireDeclCommand = _init_l_Lake_DSL_instCoeRequireDeclCommand();
lean_mark_persistent(l_Lake_DSL_instCoeRequireDeclCommand);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
