// Lean compiler output
// Module: Lean.Elab.MatchExpr
// Imports: Lean.Elab.Term
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandLetExpr__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Lean_Elab_Term_MatchExpr_next_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("matchExprElseAlt", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = lean_mk_string_unchecked("hole", 4, 4);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_4);
x_16 = l_Lean_Syntax_isOfKind(x_4, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
x_7 = x_17;
goto block_10;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_box(0);
x_7 = x_18;
goto block_10;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toAlt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("matchExprAlt", 12, 12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_31 = lean_mk_string_unchecked("matchExprPat", 12, 12);
x_32 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_31);
lean_inc(x_10);
x_33 = l_Lean_Syntax_isOfKind(x_10, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_1);
x_34 = lean_box(0);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_10, x_35);
x_37 = l_Lean_Syntax_isNone(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(2u);
lean_inc(x_36);
x_39 = l_Lean_Syntax_matchesNull(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_10);
lean_dec(x_1);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Syntax_getArg(x_36, x_35);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_11 = x_42;
goto block_30;
}
}
else
{
lean_object* x_43; 
lean_dec(x_36);
x_43 = lean_box(0);
x_11 = x_43;
goto block_30;
}
}
block_30:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Syntax_getArg(x_10, x_9);
x_13 = lean_mk_string_unchecked("ident", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_10, x_17);
lean_dec(x_10);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_array_to_list(x_19);
x_21 = l_List_reverse___redArg(x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(x_21, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set(x_28, 5, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uget(x_2, x_4);
x_9 = l_Lean_Syntax_getId(x_8);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_Syntax_getId(x_10);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = l_List_isEmpty___redArg(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_free_object(x_1);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_14);
x_16 = lean_array_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(x_4, x_2, x_16, x_18, x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
goto block_12;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
goto block_12;
}
else
{
lean_dec(x_21);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
}
}
block_12:
{
if (x_7 == 0)
{
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_array_push(x_2, x_9);
x_1 = x_5;
x_2 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = l_List_isEmpty___redArg(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_23);
x_1 = x_24;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_size(x_2);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_usize_of_nat(x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(x_23, x_2, x_36, x_38, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
goto block_31;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
goto block_31;
}
else
{
lean_dec(x_41);
lean_dec(x_23);
x_1 = x_24;
goto _start;
}
}
}
block_31:
{
if (x_26 == 0)
{
lean_dec(x_23);
x_1 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_array_push(x_2, x_28);
x_1 = x_24;
x_2 = x_29;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = l_List_isEmpty___redArg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_14; 
lean_free_object(x_2);
lean_dec(x_5);
x_14 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_6, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_box(0);
x_16 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_array_size(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(x_5, x_3, x_17, x_19, x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
goto block_13;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
goto block_13;
}
else
{
lean_object* x_23; 
lean_dec(x_22);
lean_dec(x_5);
x_23 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_6, x_3);
return x_23;
}
}
}
block_13:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_6, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_push(x_3, x_10);
x_12 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_6, x_11);
return x_12;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = l_List_isEmpty___redArg(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_33; 
lean_dec(x_24);
x_33 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_25, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_size(x_3);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_usize_of_nat(x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(x_24, x_3, x_37, x_39, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
goto block_32;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
goto block_32;
}
else
{
lean_object* x_43; 
lean_dec(x_42);
lean_dec(x_24);
x_43 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_25, x_3);
return x_43;
}
}
}
block_32:
{
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
x_28 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_25, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_array_push(x_3, x_29);
x_31 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___redArg(x_25, x_30);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_inc(x_1);
x_4 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(x_1, x_1, x_3);
lean_dec(x_1);
x_5 = lean_array_to_list(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_shouldSaveActual(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed), 1, 0);
x_3 = l_List_any___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_MatchExpr_shouldSaveActual___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_Syntax_getId(x_3);
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_List_isEmpty___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_find_x3f(lean_box(0), x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Lean_Elab_Term_MatchExpr_next_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_array_to_list(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_23; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
goto block_22;
}
else
{
uint8_t x_25; 
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 5);
lean_inc(x_32);
lean_dec(x_5);
lean_inc(x_1);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_1);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_23);
x_7 = x_33;
goto block_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_5, 5);
lean_inc(x_39);
lean_dec(x_5);
lean_inc(x_1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_40);
x_7 = x_41;
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; 
x_8 = lean_array_push(x_3, x_7);
x_2 = x_6;
x_3 = x_8;
goto _start;
}
block_22:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 5);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
x_7 = x_20;
goto block_10;
}
else
{
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_next(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_List_filterMapTR_go___at___Lean_Elab_Term_MatchExpr_next_spec__0(x_2, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_SourceInfo_fromRef(x_10, x_12);
lean_dec(x_10);
x_14 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_14);
x_15 = l_String_toSubstring_x27(x_14);
x_16 = l_Lean_Name_mkStr1(x_14);
x_17 = l_Lean_addMacroScope(x_9, x_16, x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_1, 5);
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
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_initK___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_MatchExpr_initK(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
x_7 = x_4;
x_8 = x_6;
goto block_13;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_5, 5);
lean_inc(x_18);
x_19 = l_Lean_SourceInfo_fromRef(x_18, x_14);
lean_dec(x_18);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Term", 4, 4);
x_25 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_22);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_19);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
lean_inc(x_30);
lean_inc(x_19);
x_31 = l_Lean_Syntax_node1(x_19, x_30, x_17);
x_32 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_19);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("Expr", 4, 4);
lean_inc(x_34);
x_35 = l_String_toSubstring_x27(x_34);
lean_inc(x_34);
x_36 = l_Lean_Name_mkStr1(x_34);
x_37 = l_Lean_addMacroScope(x_21, x_36, x_20);
x_38 = l_Lean_Name_mkStr2(x_22, x_34);
x_39 = lean_box(0);
lean_inc(x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_38);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_19);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_43);
lean_inc(x_30);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node2(x_19, x_30, x_33, x_44);
x_46 = l_Array_mkArray0(lean_box(0));
lean_inc(x_19);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_30);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_19);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Syntax_node5(x_19, x_26, x_28, x_31, x_45, x_47, x_49);
x_51 = lean_array_push(x_4, x_50);
x_7 = x_51;
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_ctor_get(x_5, 5);
lean_inc(x_53);
x_54 = l_Lean_SourceInfo_fromRef(x_53, x_14);
lean_dec(x_53);
x_55 = lean_ctor_get(x_5, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
x_57 = lean_mk_string_unchecked("Lean", 4, 4);
x_58 = lean_mk_string_unchecked("Parser", 6, 6);
x_59 = lean_mk_string_unchecked("Term", 4, 4);
x_60 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_57);
x_61 = l_Lean_Name_mkStr4(x_57, x_58, x_59, x_60);
x_62 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_54);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
lean_inc(x_65);
lean_inc(x_54);
x_66 = l_Lean_Syntax_node1(x_54, x_65, x_52);
x_67 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_54);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("Expr", 4, 4);
lean_inc(x_69);
x_70 = l_String_toSubstring_x27(x_69);
lean_inc(x_69);
x_71 = l_Lean_Name_mkStr1(x_69);
x_72 = l_Lean_addMacroScope(x_56, x_71, x_55);
x_73 = l_Lean_Name_mkStr2(x_57, x_69);
x_74 = lean_box(0);
lean_inc(x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_54);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_54);
lean_ctor_set(x_80, 1, x_70);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_79);
lean_inc(x_65);
lean_inc(x_54);
x_81 = l_Lean_Syntax_node2(x_54, x_65, x_68, x_80);
x_82 = l_Array_mkArray0(lean_box(0));
lean_inc(x_54);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_54);
lean_ctor_set(x_83, 1, x_65);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_54);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_54);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Syntax_node5(x_54, x_61, x_63, x_66, x_81, x_83, x_85);
x_87 = lean_array_push(x_4, x_86);
x_7 = x_87;
x_8 = x_6;
goto block_13;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_5);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_4);
lean_ctor_set(x_88, 1, x_6);
return x_88;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_nat_dec_lt(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_le(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_2);
x_14 = lean_usize_of_nat(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(x_1, x_13, x_14, x_7, x_4, x_5);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_6, x_2, x_7);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_mk_empty_array_with_capacity(x_116);
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
x_4 = x_117;
x_5 = x_2;
x_6 = x_3;
goto block_115;
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_2, 5);
lean_inc(x_121);
x_122 = lean_box(0);
x_123 = lean_unbox(x_122);
x_124 = l_Lean_SourceInfo_fromRef(x_121, x_123);
lean_dec(x_121);
x_125 = lean_ctor_get(x_2, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
x_127 = lean_mk_string_unchecked("Lean", 4, 4);
x_128 = lean_mk_string_unchecked("Parser", 6, 6);
x_129 = lean_mk_string_unchecked("Term", 4, 4);
x_130 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_127);
x_131 = l_Lean_Name_mkStr4(x_127, x_128, x_129, x_130);
x_132 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_124);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("null", 4, 4);
x_135 = l_Lean_Name_mkStr1(x_134);
lean_inc(x_135);
lean_inc(x_124);
x_136 = l_Lean_Syntax_node1(x_124, x_135, x_120);
x_137 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_124);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_mk_string_unchecked("Expr", 4, 4);
lean_inc(x_139);
x_140 = l_String_toSubstring_x27(x_139);
lean_inc(x_139);
x_141 = l_Lean_Name_mkStr1(x_139);
x_142 = l_Lean_addMacroScope(x_126, x_141, x_125);
x_143 = l_Lean_Name_mkStr2(x_127, x_139);
x_144 = lean_box(0);
lean_inc(x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_tag(x_118, 0);
lean_ctor_set(x_118, 0, x_143);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_118);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_124);
x_149 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_149, 0, x_124);
lean_ctor_set(x_149, 1, x_140);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_148);
lean_inc(x_135);
lean_inc(x_124);
x_150 = l_Lean_Syntax_node2(x_124, x_135, x_138, x_149);
x_151 = l_Array_mkArray0(lean_box(0));
lean_inc(x_124);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_124);
lean_ctor_set(x_152, 1, x_135);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_124);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_124);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Syntax_node5(x_124, x_131, x_133, x_136, x_150, x_152, x_154);
x_156 = lean_array_push(x_117, x_155);
x_4 = x_156;
x_5 = x_2;
x_6 = x_3;
goto block_115;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_157 = lean_ctor_get(x_118, 0);
lean_inc(x_157);
lean_dec(x_118);
x_158 = lean_ctor_get(x_2, 5);
lean_inc(x_158);
x_159 = lean_box(0);
x_160 = lean_unbox(x_159);
x_161 = l_Lean_SourceInfo_fromRef(x_158, x_160);
lean_dec(x_158);
x_162 = lean_ctor_get(x_2, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_2, 1);
lean_inc(x_163);
x_164 = lean_mk_string_unchecked("Lean", 4, 4);
x_165 = lean_mk_string_unchecked("Parser", 6, 6);
x_166 = lean_mk_string_unchecked("Term", 4, 4);
x_167 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_164);
x_168 = l_Lean_Name_mkStr4(x_164, x_165, x_166, x_167);
x_169 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_161);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_mk_string_unchecked("null", 4, 4);
x_172 = l_Lean_Name_mkStr1(x_171);
lean_inc(x_172);
lean_inc(x_161);
x_173 = l_Lean_Syntax_node1(x_161, x_172, x_157);
x_174 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_161);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_string_unchecked("Expr", 4, 4);
lean_inc(x_176);
x_177 = l_String_toSubstring_x27(x_176);
lean_inc(x_176);
x_178 = l_Lean_Name_mkStr1(x_176);
x_179 = l_Lean_addMacroScope(x_163, x_178, x_162);
x_180 = l_Lean_Name_mkStr2(x_164, x_176);
x_181 = lean_box(0);
lean_inc(x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_180);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_161);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_161);
lean_ctor_set(x_187, 1, x_177);
lean_ctor_set(x_187, 2, x_179);
lean_ctor_set(x_187, 3, x_186);
lean_inc(x_172);
lean_inc(x_161);
x_188 = l_Lean_Syntax_node2(x_161, x_172, x_175, x_187);
x_189 = l_Array_mkArray0(lean_box(0));
lean_inc(x_161);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_161);
lean_ctor_set(x_190, 1, x_172);
lean_ctor_set(x_190, 2, x_189);
x_191 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_161);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_161);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Syntax_node5(x_161, x_168, x_170, x_173, x_188, x_190, x_192);
x_194 = lean_array_push(x_117, x_193);
x_4 = x_194;
x_5 = x_2;
x_6 = x_3;
goto block_115;
}
}
block_115:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_mk(x_7);
x_9 = l_Array_reverse(lean_box(0), x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
lean_inc(x_5);
x_12 = l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0(x_9, x_10, x_11, x_5, x_6);
lean_dec(x_11);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Array_append(lean_box(0), x_4, x_14);
lean_dec(x_14);
x_16 = l_Array_isEmpty___redArg(x_15);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_5);
x_17 = lean_array_size(x_15);
x_18 = lean_usize_of_nat(x_10);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2(x_17, x_18, x_15);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_15);
x_20 = lean_ctor_get(x_5, 5);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_SourceInfo_fromRef(x_20, x_22);
lean_dec(x_20);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Parser", 6, 6);
x_28 = lean_mk_string_unchecked("Term", 4, 4);
x_29 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
x_31 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_23);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("null", 4, 4);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_mk_string_unchecked("hole", 4, 4);
x_36 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_35);
x_37 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_23);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_23);
x_39 = l_Lean_Syntax_node1(x_23, x_36, x_38);
lean_inc(x_34);
lean_inc(x_23);
x_40 = l_Lean_Syntax_node1(x_23, x_34, x_39);
x_41 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_23);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_43);
x_44 = l_String_toSubstring_x27(x_43);
x_45 = l_Lean_Name_mkStr1(x_43);
lean_inc(x_45);
x_46 = l_Lean_addMacroScope(x_25, x_45, x_24);
x_47 = lean_box(0);
lean_inc(x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_23);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
lean_inc(x_34);
lean_inc(x_23);
x_54 = l_Lean_Syntax_node2(x_23, x_34, x_42, x_53);
x_55 = l_Array_mkArray0(lean_box(0));
lean_inc(x_23);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_23);
lean_ctor_set(x_56, 1, x_34);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_23);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Syntax_node5(x_23, x_30, x_32, x_40, x_54, x_56, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
x_62 = lean_array_push(x_61, x_59);
lean_ctor_set(x_12, 0, x_62);
return x_12;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = l_Array_append(lean_box(0), x_4, x_63);
lean_dec(x_63);
x_66 = l_Array_isEmpty___redArg(x_65);
if (x_66 == 0)
{
size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
x_67 = lean_array_size(x_65);
x_68 = lean_usize_of_nat(x_10);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2(x_67, x_68, x_65);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_65);
x_71 = lean_ctor_get(x_5, 5);
lean_inc(x_71);
x_72 = lean_box(0);
x_73 = lean_unbox(x_72);
x_74 = l_Lean_SourceInfo_fromRef(x_71, x_73);
lean_dec(x_71);
x_75 = lean_ctor_get(x_5, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_5, 1);
lean_inc(x_76);
lean_dec(x_5);
x_77 = lean_mk_string_unchecked("Lean", 4, 4);
x_78 = lean_mk_string_unchecked("Parser", 6, 6);
x_79 = lean_mk_string_unchecked("Term", 4, 4);
x_80 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_81 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_80);
x_82 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_74);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("null", 4, 4);
x_85 = l_Lean_Name_mkStr1(x_84);
x_86 = lean_mk_string_unchecked("hole", 4, 4);
x_87 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_86);
x_88 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_74);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_74);
x_90 = l_Lean_Syntax_node1(x_74, x_87, x_89);
lean_inc(x_85);
lean_inc(x_74);
x_91 = l_Lean_Syntax_node1(x_74, x_85, x_90);
x_92 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_74);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_74);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_94);
x_95 = l_String_toSubstring_x27(x_94);
x_96 = l_Lean_Name_mkStr1(x_94);
lean_inc(x_96);
x_97 = l_Lean_addMacroScope(x_76, x_96, x_75);
x_98 = lean_box(0);
lean_inc(x_96);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_96);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_74);
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_74);
lean_ctor_set(x_104, 1, x_95);
lean_ctor_set(x_104, 2, x_97);
lean_ctor_set(x_104, 3, x_103);
lean_inc(x_85);
lean_inc(x_74);
x_105 = l_Lean_Syntax_node2(x_74, x_85, x_93, x_104);
x_106 = l_Array_mkArray0(lean_box(0));
lean_inc(x_74);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_74);
lean_ctor_set(x_107, 1, x_85);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_74);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_74);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Syntax_node5(x_74, x_81, x_83, x_91, x_105, x_107, x_109);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_mk_empty_array_with_capacity(x_111);
x_113 = lean_array_push(x_112, x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_64);
return x_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMapM___at___Lean_Elab_Term_MatchExpr_getParams_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_MatchExpr_getParams_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_mk_empty_array_with_capacity(x_36);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_1);
x_5 = x_37;
x_6 = x_3;
x_7 = x_4;
goto block_35;
}
else
{
lean_object* x_39; 
lean_dec(x_38);
x_39 = lean_array_push(x_37, x_1);
x_5 = x_39;
x_6 = x_3;
x_7 = x_4;
goto block_35;
}
block_35:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_mk(x_8);
x_10 = l_Array_append(lean_box(0), x_5, x_9);
lean_dec(x_9);
x_11 = l_Array_isEmpty___redArg(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_SourceInfo_fromRef(x_13, x_15);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("tuple", 5, 5);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_16);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Array_mkArray0(lean_box(0));
lean_inc(x_16);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_16);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Syntax_node3(x_16, x_21, x_23, x_27, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_array_push(x_32, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_getActuals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_MatchExpr_getActuals(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doubleQuotedName", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`", 1, 1);
x_8 = l_Lean_mkAtom(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_8);
x_11 = lean_array_push(x_10, x_8);
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_box(2);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(x_1, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_free_object(x_3);
lean_dec(x_9);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_MatchExpr_getActuals(x_2, x_13, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_5, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_5, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_21);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_21);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_29 = lean_mk_string_unchecked("Term", 4, 4);
x_30 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_33 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_32);
x_34 = lean_mk_string_unchecked("paren", 5, 5);
x_35 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_34);
x_36 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_21);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_36);
lean_ctor_set(x_3, 0, x_21);
x_37 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_21);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_2);
lean_inc(x_21);
x_39 = l_Lean_Syntax_node3(x_21, x_35, x_3, x_2, x_38);
x_40 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_21);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked("isConstOf", 9, 9);
lean_inc(x_42);
x_43 = l_String_toSubstring_x27(x_42);
x_44 = l_Lean_Name_mkStr1(x_42);
x_45 = l_Lean_addMacroScope(x_23, x_44, x_22);
x_46 = lean_box(0);
lean_inc(x_21);
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
lean_inc(x_21);
x_48 = l_Lean_Syntax_node3(x_21, x_33, x_39, x_41, x_47);
x_49 = lean_mk_string_unchecked("null", 4, 4);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(x_9);
lean_inc(x_50);
lean_inc(x_21);
x_52 = l_Lean_Syntax_node1(x_21, x_50, x_51);
lean_inc(x_31);
lean_inc(x_21);
x_53 = l_Lean_Syntax_node2(x_21, x_31, x_48, x_52);
x_54 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_21);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_21);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_ctor_get(x_13, 4);
lean_inc(x_56);
lean_dec(x_13);
x_57 = l_Array_mkArray0(lean_box(0));
x_58 = l_Array_append(lean_box(0), x_57, x_16);
lean_dec(x_16);
lean_inc(x_21);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_21);
lean_ctor_set(x_59, 1, x_50);
lean_ctor_set(x_59, 2, x_58);
lean_inc(x_21);
x_60 = l_Lean_Syntax_node2(x_21, x_31, x_56, x_59);
x_61 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_21);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_21);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Syntax_node6(x_21, x_25, x_14, x_53, x_55, x_60, x_62, x_4);
x_3 = x_10;
x_4 = x_63;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_14);
x_67 = lean_ctor_get(x_5, 5);
lean_inc(x_67);
x_68 = lean_box(0);
x_69 = lean_unbox(x_68);
x_70 = l_Lean_SourceInfo_fromRef(x_67, x_69);
lean_dec(x_67);
x_71 = lean_ctor_get(x_5, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 1);
lean_inc(x_72);
x_73 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_70);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("Lean", 4, 4);
x_78 = lean_mk_string_unchecked("Parser", 6, 6);
x_79 = lean_mk_string_unchecked("Term", 4, 4);
x_80 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_81 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_80);
x_82 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_83 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_82);
x_84 = lean_mk_string_unchecked("paren", 5, 5);
x_85 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_84);
x_86 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_70);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_86);
lean_ctor_set(x_3, 0, x_70);
x_87 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_70);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_2);
lean_inc(x_70);
x_89 = l_Lean_Syntax_node3(x_70, x_85, x_3, x_2, x_88);
x_90 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_70);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("isConstOf", 9, 9);
lean_inc(x_92);
x_93 = l_String_toSubstring_x27(x_92);
x_94 = l_Lean_Name_mkStr1(x_92);
x_95 = l_Lean_addMacroScope(x_72, x_94, x_71);
x_96 = lean_box(0);
lean_inc(x_70);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_70);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
lean_inc(x_70);
x_98 = l_Lean_Syntax_node3(x_70, x_83, x_89, x_91, x_97);
x_99 = lean_mk_string_unchecked("null", 4, 4);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(x_9);
lean_inc(x_100);
lean_inc(x_70);
x_102 = l_Lean_Syntax_node1(x_70, x_100, x_101);
lean_inc(x_81);
lean_inc(x_70);
x_103 = l_Lean_Syntax_node2(x_70, x_81, x_98, x_102);
x_104 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_70);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_70);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_ctor_get(x_13, 4);
lean_inc(x_106);
lean_dec(x_13);
x_107 = l_Array_mkArray0(lean_box(0));
x_108 = l_Array_append(lean_box(0), x_107, x_65);
lean_dec(x_65);
lean_inc(x_70);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_70);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_108);
lean_inc(x_70);
x_110 = l_Lean_Syntax_node2(x_70, x_81, x_106, x_109);
x_111 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_70);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_70);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Syntax_node6(x_70, x_74, x_76, x_103, x_105, x_110, x_112, x_4);
x_3 = x_10;
x_4 = x_113;
x_6 = x_66;
goto _start;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_3, 0);
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_3);
lean_inc(x_115);
lean_inc(x_1);
x_117 = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(x_1, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_dec(x_115);
x_3 = x_116;
goto _start;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_119);
lean_inc(x_2);
x_120 = l_Lean_Elab_Term_MatchExpr_getActuals(x_2, x_119, x_5, x_6);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_5, 5);
lean_inc(x_124);
x_125 = lean_box(0);
x_126 = lean_unbox(x_125);
x_127 = l_Lean_SourceInfo_fromRef(x_124, x_126);
lean_dec(x_124);
x_128 = lean_ctor_get(x_5, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_5, 1);
lean_inc(x_129);
x_130 = lean_mk_string_unchecked("termIfThenElse", 14, 14);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_127);
if (lean_is_scalar(x_123)) {
 x_133 = lean_alloc_ctor(2, 2, 0);
} else {
 x_133 = x_123;
 lean_ctor_set_tag(x_133, 2);
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("Lean", 4, 4);
x_135 = lean_mk_string_unchecked("Parser", 6, 6);
x_136 = lean_mk_string_unchecked("Term", 4, 4);
x_137 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
x_138 = l_Lean_Name_mkStr4(x_134, x_135, x_136, x_137);
x_139 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
x_140 = l_Lean_Name_mkStr4(x_134, x_135, x_136, x_139);
x_141 = lean_mk_string_unchecked("paren", 5, 5);
x_142 = l_Lean_Name_mkStr4(x_134, x_135, x_136, x_141);
x_143 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_127);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_127);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_127);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_127);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_2);
lean_inc(x_127);
x_147 = l_Lean_Syntax_node3(x_127, x_142, x_144, x_2, x_146);
x_148 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_127);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_127);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("isConstOf", 9, 9);
lean_inc(x_150);
x_151 = l_String_toSubstring_x27(x_150);
x_152 = l_Lean_Name_mkStr1(x_150);
x_153 = l_Lean_addMacroScope(x_129, x_152, x_128);
x_154 = lean_box(0);
lean_inc(x_127);
x_155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_155, 0, x_127);
lean_ctor_set(x_155, 1, x_151);
lean_ctor_set(x_155, 2, x_153);
lean_ctor_set(x_155, 3, x_154);
lean_inc(x_127);
x_156 = l_Lean_Syntax_node3(x_127, x_140, x_147, x_149, x_155);
x_157 = lean_mk_string_unchecked("null", 4, 4);
x_158 = l_Lean_Name_mkStr1(x_157);
x_159 = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(x_115);
lean_inc(x_158);
lean_inc(x_127);
x_160 = l_Lean_Syntax_node1(x_127, x_158, x_159);
lean_inc(x_138);
lean_inc(x_127);
x_161 = l_Lean_Syntax_node2(x_127, x_138, x_156, x_160);
x_162 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_127);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_127);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_ctor_get(x_119, 4);
lean_inc(x_164);
lean_dec(x_119);
x_165 = l_Array_mkArray0(lean_box(0));
x_166 = l_Array_append(lean_box(0), x_165, x_121);
lean_dec(x_121);
lean_inc(x_127);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_127);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_166);
lean_inc(x_127);
x_168 = l_Lean_Syntax_node2(x_127, x_138, x_164, x_167);
x_169 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_127);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_127);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Syntax_node6(x_127, x_131, x_133, x_161, x_163, x_168, x_170, x_4);
x_3 = x_116;
x_4 = x_171;
x_6 = x_122;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_1, x_2, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_inc(x_3);
x_6 = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(x_3);
lean_inc(x_3);
x_7 = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(x_3);
x_923 = lean_ctor_get(x_5, 0);
lean_inc(x_923);
x_924 = lean_unsigned_to_nat(1u);
x_925 = lean_nat_add(x_923, x_924);
x_926 = lean_ctor_get(x_5, 1);
lean_inc(x_926);
lean_dec(x_5);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_925);
lean_ctor_set(x_927, 1, x_926);
x_928 = lean_ctor_get(x_4, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_4, 1);
lean_inc(x_929);
x_930 = lean_ctor_get(x_4, 3);
lean_inc(x_930);
x_931 = lean_ctor_get(x_4, 4);
lean_inc(x_931);
x_932 = lean_ctor_get(x_4, 5);
lean_inc(x_932);
lean_dec(x_4);
lean_inc(x_932);
lean_inc(x_923);
lean_inc(x_929);
x_933 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_933, 0, x_928);
lean_ctor_set(x_933, 1, x_929);
lean_ctor_set(x_933, 2, x_923);
lean_ctor_set(x_933, 3, x_930);
lean_ctor_set(x_933, 4, x_931);
lean_ctor_set(x_933, 5, x_932);
if (x_7 == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_929);
lean_dec(x_923);
x_934 = l_Lean_SourceInfo_fromRef(x_932, x_7);
lean_dec(x_932);
x_935 = lean_mk_string_unchecked("Lean", 4, 4);
x_936 = lean_mk_string_unchecked("Parser", 6, 6);
x_937 = lean_mk_string_unchecked("Term", 4, 4);
x_938 = lean_mk_string_unchecked("hole", 4, 4);
x_939 = l_Lean_Name_mkStr4(x_935, x_936, x_937, x_938);
x_940 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_934);
x_941 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_941, 0, x_934);
lean_ctor_set(x_941, 1, x_940);
x_942 = l_Lean_Syntax_node1(x_934, x_939, x_941);
x_8 = x_942;
x_9 = x_933;
x_10 = x_927;
goto block_922;
}
else
{
lean_object* x_943; uint8_t x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_943 = lean_box(0);
x_944 = lean_unbox(x_943);
x_945 = l_Lean_SourceInfo_fromRef(x_932, x_944);
lean_dec(x_932);
x_946 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_946);
x_947 = l_String_toSubstring_x27(x_946);
x_948 = l_Lean_Name_mkStr1(x_946);
x_949 = l_Lean_addMacroScope(x_929, x_948, x_923);
x_950 = lean_box(0);
x_951 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_951, 0, x_945);
lean_ctor_set(x_951, 1, x_947);
lean_ctor_set(x_951, 2, x_949);
lean_ctor_set(x_951, 3, x_950);
x_8 = x_951;
x_9 = x_933;
x_10 = x_927;
goto block_922;
}
block_922:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_MatchExpr_next(x_3, x_8);
x_12 = l_List_isEmpty___redArg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_9, 5);
lean_inc(x_13);
x_14 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_12, x_13, x_9, x_10);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_9, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_20);
x_21 = l_String_toSubstring_x27(x_20);
x_22 = l_Lean_Name_mkStr1(x_20);
lean_inc(x_18);
lean_inc(x_19);
x_23 = l_Lean_addMacroScope(x_19, x_22, x_18);
x_24 = lean_box(0);
lean_inc(x_23);
lean_inc(x_21);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_9);
lean_inc(x_1);
x_26 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_1, x_25, x_11, x_9, x_17);
if (x_7 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Lean_SourceInfo_fromRef(x_32, x_12);
lean_dec(x_32);
x_35 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_34);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_37);
lean_ctor_set(x_30, 0, x_34);
x_38 = lean_mk_string_unchecked("Lean", 4, 4);
x_39 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_38);
x_40 = l_Lean_Name_mkStr2(x_38, x_39);
x_41 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_41);
x_42 = l_String_toSubstring_x27(x_41);
x_43 = l_Lean_Name_mkStr1(x_41);
lean_inc(x_18);
lean_inc(x_19);
x_44 = l_Lean_addMacroScope(x_19, x_43, x_18);
lean_inc(x_34);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_24);
lean_inc(x_45);
lean_inc(x_34);
x_46 = l_Lean_Syntax_node1(x_34, x_40, x_45);
x_47 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_34);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_47);
lean_ctor_set(x_26, 0, x_34);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Term", 4, 4);
x_50 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_51 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_50);
x_52 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_53 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_52);
x_54 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_34);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_54);
lean_ctor_set(x_14, 0, x_34);
x_55 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_34);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_34);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_56);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_34);
x_57 = l_Lean_Syntax_node3(x_34, x_53, x_14, x_2, x_56);
x_58 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_34);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_60);
x_61 = l_String_toSubstring_x27(x_60);
x_62 = l_Lean_Name_mkStr1(x_60);
lean_inc(x_18);
lean_inc(x_19);
x_63 = l_Lean_addMacroScope(x_19, x_62, x_18);
lean_inc(x_34);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_24);
lean_inc(x_34);
x_65 = l_Lean_Syntax_node3(x_34, x_51, x_57, x_59, x_64);
x_66 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_34);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_34);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_68);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_69 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_68);
lean_inc(x_34);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_34);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_72 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_71);
x_73 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_74 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_73);
lean_inc(x_34);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_34);
lean_ctor_set(x_75, 1, x_21);
lean_ctor_set(x_75, 2, x_23);
lean_ctor_set(x_75, 3, x_24);
x_76 = lean_mk_string_unchecked("null", 4, 4);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = l_Array_mkArray0(lean_box(0));
lean_inc(x_77);
lean_inc(x_34);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_34);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_34);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_34);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_38);
x_83 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_82);
x_84 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_85 = l_String_toSubstring_x27(x_84);
x_86 = lean_mk_string_unchecked("Expr", 4, 4);
x_87 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_87);
lean_inc(x_86);
x_88 = l_Lean_Name_mkStr2(x_86, x_87);
x_89 = l_Lean_addMacroScope(x_19, x_88, x_18);
lean_inc(x_38);
x_90 = l_Lean_Name_mkStr3(x_38, x_86, x_87);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_24);
lean_inc(x_34);
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_34);
lean_ctor_set(x_94, 1, x_85);
lean_ctor_set(x_94, 2, x_89);
lean_ctor_set(x_94, 3, x_93);
lean_inc(x_2);
lean_inc(x_77);
lean_inc(x_34);
x_95 = l_Lean_Syntax_node2(x_34, x_77, x_2, x_45);
lean_inc(x_83);
lean_inc(x_34);
x_96 = l_Lean_Syntax_node2(x_34, x_83, x_94, x_95);
lean_inc_n(x_79, 2);
lean_inc(x_34);
x_97 = l_Lean_Syntax_node5(x_34, x_74, x_75, x_79, x_79, x_81, x_96);
lean_inc(x_34);
x_98 = l_Lean_Syntax_node1(x_34, x_72, x_97);
x_99 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_34);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_34);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_34);
x_101 = l_Lean_Syntax_node4(x_34, x_69, x_70, x_98, x_100, x_28);
x_102 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_34);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_34);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("tuple", 5, 5);
x_105 = l_Lean_Name_mkStr4(x_38, x_48, x_49, x_104);
lean_inc(x_34);
x_106 = l_Lean_Syntax_node3(x_34, x_105, x_14, x_79, x_56);
lean_inc(x_34);
x_107 = l_Lean_Syntax_node1(x_34, x_77, x_106);
lean_inc(x_34);
x_108 = l_Lean_Syntax_node2(x_34, x_83, x_1, x_107);
x_109 = l_Lean_Syntax_node8(x_34, x_36, x_30, x_46, x_26, x_65, x_67, x_101, x_103, x_108);
x_110 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_109, x_9, x_33);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_111 = lean_ctor_get(x_30, 0);
x_112 = lean_ctor_get(x_30, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_30);
x_113 = l_Lean_SourceInfo_fromRef(x_111, x_12);
lean_dec(x_111);
x_114 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_113);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("Lean", 4, 4);
x_119 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_118);
x_120 = l_Lean_Name_mkStr2(x_118, x_119);
x_121 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_121);
x_122 = l_String_toSubstring_x27(x_121);
x_123 = l_Lean_Name_mkStr1(x_121);
lean_inc(x_18);
lean_inc(x_19);
x_124 = l_Lean_addMacroScope(x_19, x_123, x_18);
lean_inc(x_113);
x_125 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_24);
lean_inc(x_125);
lean_inc(x_113);
x_126 = l_Lean_Syntax_node1(x_113, x_120, x_125);
x_127 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_113);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_127);
lean_ctor_set(x_26, 0, x_113);
x_128 = lean_mk_string_unchecked("Parser", 6, 6);
x_129 = lean_mk_string_unchecked("Term", 4, 4);
x_130 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_131 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_130);
x_132 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_133 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_132);
x_134 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_113);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_134);
lean_ctor_set(x_14, 0, x_113);
x_135 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_113);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_113);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_136);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_113);
x_137 = l_Lean_Syntax_node3(x_113, x_133, x_14, x_2, x_136);
x_138 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_113);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_113);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_140);
x_141 = l_String_toSubstring_x27(x_140);
x_142 = l_Lean_Name_mkStr1(x_140);
lean_inc(x_18);
lean_inc(x_19);
x_143 = l_Lean_addMacroScope(x_19, x_142, x_18);
lean_inc(x_113);
x_144 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_144, 0, x_113);
lean_ctor_set(x_144, 1, x_141);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_24);
lean_inc(x_113);
x_145 = l_Lean_Syntax_node3(x_113, x_131, x_137, x_139, x_144);
x_146 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_113);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_113);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_148);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_149 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_148);
lean_inc(x_113);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_113);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_152 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_151);
x_153 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_154 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_153);
lean_inc(x_113);
x_155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_155, 0, x_113);
lean_ctor_set(x_155, 1, x_21);
lean_ctor_set(x_155, 2, x_23);
lean_ctor_set(x_155, 3, x_24);
x_156 = lean_mk_string_unchecked("null", 4, 4);
x_157 = l_Lean_Name_mkStr1(x_156);
x_158 = l_Array_mkArray0(lean_box(0));
lean_inc(x_157);
lean_inc(x_113);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_113);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_113);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_113);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_118);
x_163 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_162);
x_164 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_165 = l_String_toSubstring_x27(x_164);
x_166 = lean_mk_string_unchecked("Expr", 4, 4);
x_167 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_167);
lean_inc(x_166);
x_168 = l_Lean_Name_mkStr2(x_166, x_167);
x_169 = l_Lean_addMacroScope(x_19, x_168, x_18);
lean_inc(x_118);
x_170 = l_Lean_Name_mkStr3(x_118, x_166, x_167);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_24);
lean_inc(x_113);
x_174 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_174, 0, x_113);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_169);
lean_ctor_set(x_174, 3, x_173);
lean_inc(x_2);
lean_inc(x_157);
lean_inc(x_113);
x_175 = l_Lean_Syntax_node2(x_113, x_157, x_2, x_125);
lean_inc(x_163);
lean_inc(x_113);
x_176 = l_Lean_Syntax_node2(x_113, x_163, x_174, x_175);
lean_inc_n(x_159, 2);
lean_inc(x_113);
x_177 = l_Lean_Syntax_node5(x_113, x_154, x_155, x_159, x_159, x_161, x_176);
lean_inc(x_113);
x_178 = l_Lean_Syntax_node1(x_113, x_152, x_177);
x_179 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_113);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_113);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_113);
x_181 = l_Lean_Syntax_node4(x_113, x_149, x_150, x_178, x_180, x_28);
x_182 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_113);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_113);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_mk_string_unchecked("tuple", 5, 5);
x_185 = l_Lean_Name_mkStr4(x_118, x_128, x_129, x_184);
lean_inc(x_113);
x_186 = l_Lean_Syntax_node3(x_113, x_185, x_14, x_159, x_136);
lean_inc(x_113);
x_187 = l_Lean_Syntax_node1(x_113, x_157, x_186);
lean_inc(x_113);
x_188 = l_Lean_Syntax_node2(x_113, x_163, x_1, x_187);
x_189 = l_Lean_Syntax_node8(x_113, x_115, x_117, x_126, x_26, x_145, x_147, x_181, x_183, x_188);
x_190 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_189, x_9, x_112);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_191 = lean_ctor_get(x_26, 0);
x_192 = lean_ctor_get(x_26, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_26);
x_193 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = l_Lean_SourceInfo_fromRef(x_194, x_12);
lean_dec(x_194);
x_198 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_199 = l_Lean_Name_mkStr1(x_198);
x_200 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_197);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(2, 2, 0);
} else {
 x_201 = x_196;
 lean_ctor_set_tag(x_201, 2);
}
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_mk_string_unchecked("Lean", 4, 4);
x_203 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_202);
x_204 = l_Lean_Name_mkStr2(x_202, x_203);
x_205 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_205);
x_206 = l_String_toSubstring_x27(x_205);
x_207 = l_Lean_Name_mkStr1(x_205);
lean_inc(x_18);
lean_inc(x_19);
x_208 = l_Lean_addMacroScope(x_19, x_207, x_18);
lean_inc(x_197);
x_209 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_209, 0, x_197);
lean_ctor_set(x_209, 1, x_206);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set(x_209, 3, x_24);
lean_inc(x_209);
lean_inc(x_197);
x_210 = l_Lean_Syntax_node1(x_197, x_204, x_209);
x_211 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_197);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_197);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_mk_string_unchecked("Parser", 6, 6);
x_214 = lean_mk_string_unchecked("Term", 4, 4);
x_215 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_216 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_215);
x_217 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_218 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_217);
x_219 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_197);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_219);
lean_ctor_set(x_14, 0, x_197);
x_220 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_197);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_197);
lean_ctor_set(x_221, 1, x_220);
lean_inc(x_221);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_197);
x_222 = l_Lean_Syntax_node3(x_197, x_218, x_14, x_2, x_221);
x_223 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_197);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_197);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_225);
x_226 = l_String_toSubstring_x27(x_225);
x_227 = l_Lean_Name_mkStr1(x_225);
lean_inc(x_18);
lean_inc(x_19);
x_228 = l_Lean_addMacroScope(x_19, x_227, x_18);
lean_inc(x_197);
x_229 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_229, 0, x_197);
lean_ctor_set(x_229, 1, x_226);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_24);
lean_inc(x_197);
x_230 = l_Lean_Syntax_node3(x_197, x_216, x_222, x_224, x_229);
x_231 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_197);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_197);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_233);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_234 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_233);
lean_inc(x_197);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_197);
lean_ctor_set(x_235, 1, x_233);
x_236 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_237 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_236);
x_238 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_239 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_238);
lean_inc(x_197);
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_197);
lean_ctor_set(x_240, 1, x_21);
lean_ctor_set(x_240, 2, x_23);
lean_ctor_set(x_240, 3, x_24);
x_241 = lean_mk_string_unchecked("null", 4, 4);
x_242 = l_Lean_Name_mkStr1(x_241);
x_243 = l_Array_mkArray0(lean_box(0));
lean_inc(x_242);
lean_inc(x_197);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_197);
lean_ctor_set(x_244, 1, x_242);
lean_ctor_set(x_244, 2, x_243);
x_245 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_197);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_197);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_202);
x_248 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_247);
x_249 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_250 = l_String_toSubstring_x27(x_249);
x_251 = lean_mk_string_unchecked("Expr", 4, 4);
x_252 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_252);
lean_inc(x_251);
x_253 = l_Lean_Name_mkStr2(x_251, x_252);
x_254 = l_Lean_addMacroScope(x_19, x_253, x_18);
lean_inc(x_202);
x_255 = l_Lean_Name_mkStr3(x_202, x_251, x_252);
x_256 = lean_box(0);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_24);
lean_inc(x_197);
x_259 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_259, 0, x_197);
lean_ctor_set(x_259, 1, x_250);
lean_ctor_set(x_259, 2, x_254);
lean_ctor_set(x_259, 3, x_258);
lean_inc(x_2);
lean_inc(x_242);
lean_inc(x_197);
x_260 = l_Lean_Syntax_node2(x_197, x_242, x_2, x_209);
lean_inc(x_248);
lean_inc(x_197);
x_261 = l_Lean_Syntax_node2(x_197, x_248, x_259, x_260);
lean_inc_n(x_244, 2);
lean_inc(x_197);
x_262 = l_Lean_Syntax_node5(x_197, x_239, x_240, x_244, x_244, x_246, x_261);
lean_inc(x_197);
x_263 = l_Lean_Syntax_node1(x_197, x_237, x_262);
x_264 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_197);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_197);
lean_ctor_set(x_265, 1, x_264);
lean_inc(x_197);
x_266 = l_Lean_Syntax_node4(x_197, x_234, x_235, x_263, x_265, x_191);
x_267 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_197);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_197);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_mk_string_unchecked("tuple", 5, 5);
x_270 = l_Lean_Name_mkStr4(x_202, x_213, x_214, x_269);
lean_inc(x_197);
x_271 = l_Lean_Syntax_node3(x_197, x_270, x_14, x_244, x_221);
lean_inc(x_197);
x_272 = l_Lean_Syntax_node1(x_197, x_242, x_271);
lean_inc(x_197);
x_273 = l_Lean_Syntax_node2(x_197, x_248, x_1, x_272);
x_274 = l_Lean_Syntax_node8(x_197, x_199, x_201, x_210, x_212, x_230, x_232, x_266, x_268, x_273);
x_275 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_274, x_9, x_195);
return x_275;
}
}
else
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_26);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_277 = lean_ctor_get(x_26, 0);
x_278 = lean_ctor_get(x_26, 1);
x_279 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_278);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = lean_ctor_get(x_279, 1);
x_283 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_12, x_281, x_9, x_282);
lean_dec(x_281);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_ctor_get(x_283, 1);
x_287 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_288 = l_Lean_Name_mkStr1(x_287);
x_289 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_285);
lean_ctor_set_tag(x_283, 2);
lean_ctor_set(x_283, 1, x_289);
x_290 = lean_mk_string_unchecked("Lean", 4, 4);
x_291 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_290);
x_292 = l_Lean_Name_mkStr2(x_290, x_291);
x_293 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_293);
x_294 = l_String_toSubstring_x27(x_293);
x_295 = l_Lean_Name_mkStr1(x_293);
lean_inc(x_18);
lean_inc(x_19);
x_296 = l_Lean_addMacroScope(x_19, x_295, x_18);
lean_inc(x_285);
x_297 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_297, 0, x_285);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_296);
lean_ctor_set(x_297, 3, x_24);
lean_inc(x_297);
lean_inc(x_285);
x_298 = l_Lean_Syntax_node1(x_285, x_292, x_297);
x_299 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_285);
lean_ctor_set_tag(x_279, 2);
lean_ctor_set(x_279, 1, x_299);
lean_ctor_set(x_279, 0, x_285);
x_300 = lean_mk_string_unchecked("Parser", 6, 6);
x_301 = lean_mk_string_unchecked("Term", 4, 4);
x_302 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_303 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_302);
x_304 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_305 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_304);
x_306 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_285);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_306);
lean_ctor_set(x_26, 0, x_285);
x_307 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_285);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_307);
lean_ctor_set(x_14, 0, x_285);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_26);
lean_inc(x_285);
x_308 = l_Lean_Syntax_node3(x_285, x_305, x_26, x_2, x_14);
x_309 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_285);
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_285);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_311);
x_312 = l_String_toSubstring_x27(x_311);
x_313 = l_Lean_Name_mkStr1(x_311);
lean_inc(x_18);
lean_inc(x_19);
x_314 = l_Lean_addMacroScope(x_19, x_313, x_18);
lean_inc(x_285);
x_315 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_315, 0, x_285);
lean_ctor_set(x_315, 1, x_312);
lean_ctor_set(x_315, 2, x_314);
lean_ctor_set(x_315, 3, x_24);
lean_inc(x_285);
x_316 = l_Lean_Syntax_node3(x_285, x_303, x_308, x_310, x_315);
x_317 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_285);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_285);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_319);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_320 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_319);
lean_inc(x_285);
x_321 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_321, 0, x_285);
lean_ctor_set(x_321, 1, x_319);
x_322 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_323 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_322);
x_324 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_325 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_324);
x_326 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_326);
x_327 = l_String_toSubstring_x27(x_326);
x_328 = l_Lean_Name_mkStr1(x_326);
lean_inc(x_18);
lean_inc(x_19);
x_329 = l_Lean_addMacroScope(x_19, x_328, x_18);
lean_inc(x_285);
x_330 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_330, 0, x_285);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_329);
lean_ctor_set(x_330, 3, x_24);
x_331 = lean_mk_string_unchecked("null", 4, 4);
x_332 = l_Lean_Name_mkStr1(x_331);
x_333 = l_Array_mkArray0(lean_box(0));
lean_inc(x_332);
lean_inc(x_285);
x_334 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_334, 0, x_285);
lean_ctor_set(x_334, 1, x_332);
lean_ctor_set(x_334, 2, x_333);
x_335 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_285);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_285);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_290);
x_338 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_337);
x_339 = lean_mk_string_unchecked("Expr.appArg", 11, 11);
x_340 = l_String_toSubstring_x27(x_339);
x_341 = lean_mk_string_unchecked("Expr", 4, 4);
x_342 = lean_mk_string_unchecked("appArg", 6, 6);
lean_inc(x_342);
lean_inc(x_341);
x_343 = l_Lean_Name_mkStr2(x_341, x_342);
lean_inc(x_18);
lean_inc(x_19);
x_344 = l_Lean_addMacroScope(x_19, x_343, x_18);
lean_inc(x_341);
lean_inc(x_290);
x_345 = l_Lean_Name_mkStr3(x_290, x_341, x_342);
x_346 = lean_box(0);
lean_inc(x_345);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_348, 0, x_345);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_24);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
lean_inc(x_285);
x_351 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_351, 0, x_285);
lean_ctor_set(x_351, 1, x_340);
lean_ctor_set(x_351, 2, x_344);
lean_ctor_set(x_351, 3, x_350);
lean_inc(x_2);
lean_inc(x_332);
lean_inc(x_285);
x_352 = l_Lean_Syntax_node2(x_285, x_332, x_2, x_297);
lean_inc(x_352);
lean_inc(x_338);
lean_inc(x_285);
x_353 = l_Lean_Syntax_node2(x_285, x_338, x_351, x_352);
lean_inc(x_336);
lean_inc_n(x_334, 2);
lean_inc(x_325);
lean_inc(x_285);
x_354 = l_Lean_Syntax_node5(x_285, x_325, x_330, x_334, x_334, x_336, x_353);
lean_inc(x_323);
lean_inc(x_285);
x_355 = l_Lean_Syntax_node1(x_285, x_323, x_354);
x_356 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_285);
x_357 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_357, 0, x_285);
lean_ctor_set(x_357, 1, x_356);
lean_inc(x_285);
x_358 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_358, 0, x_285);
lean_ctor_set(x_358, 1, x_21);
lean_ctor_set(x_358, 2, x_23);
lean_ctor_set(x_358, 3, x_24);
x_359 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_360 = l_String_toSubstring_x27(x_359);
x_361 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_361);
lean_inc(x_341);
x_362 = l_Lean_Name_mkStr2(x_341, x_361);
x_363 = l_Lean_addMacroScope(x_19, x_362, x_18);
lean_inc(x_290);
x_364 = l_Lean_Name_mkStr3(x_290, x_341, x_361);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_346);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_24);
lean_inc(x_285);
x_367 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_367, 0, x_285);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_363);
lean_ctor_set(x_367, 3, x_366);
lean_inc(x_338);
lean_inc(x_285);
x_368 = l_Lean_Syntax_node2(x_285, x_338, x_367, x_352);
lean_inc_n(x_334, 2);
lean_inc(x_285);
x_369 = l_Lean_Syntax_node5(x_285, x_325, x_358, x_334, x_334, x_336, x_368);
lean_inc(x_285);
x_370 = l_Lean_Syntax_node1(x_285, x_323, x_369);
lean_inc(x_357);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_285);
x_371 = l_Lean_Syntax_node4(x_285, x_320, x_321, x_370, x_357, x_277);
lean_inc(x_285);
x_372 = l_Lean_Syntax_node4(x_285, x_320, x_321, x_355, x_357, x_371);
x_373 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_285);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_285);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_mk_string_unchecked("tuple", 5, 5);
x_376 = l_Lean_Name_mkStr4(x_290, x_300, x_301, x_375);
lean_inc(x_285);
x_377 = l_Lean_Syntax_node3(x_285, x_376, x_26, x_334, x_14);
lean_inc(x_285);
x_378 = l_Lean_Syntax_node1(x_285, x_332, x_377);
lean_inc(x_285);
x_379 = l_Lean_Syntax_node2(x_285, x_338, x_1, x_378);
x_380 = l_Lean_Syntax_node8(x_285, x_288, x_283, x_298, x_279, x_316, x_318, x_372, x_374, x_379);
x_381 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_380, x_9, x_286);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_382 = lean_ctor_get(x_283, 0);
x_383 = lean_ctor_get(x_283, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_283);
x_384 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_385 = l_Lean_Name_mkStr1(x_384);
x_386 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_382);
x_387 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_387, 0, x_382);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_mk_string_unchecked("Lean", 4, 4);
x_389 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_388);
x_390 = l_Lean_Name_mkStr2(x_388, x_389);
x_391 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_391);
x_392 = l_String_toSubstring_x27(x_391);
x_393 = l_Lean_Name_mkStr1(x_391);
lean_inc(x_18);
lean_inc(x_19);
x_394 = l_Lean_addMacroScope(x_19, x_393, x_18);
lean_inc(x_382);
x_395 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_395, 0, x_382);
lean_ctor_set(x_395, 1, x_392);
lean_ctor_set(x_395, 2, x_394);
lean_ctor_set(x_395, 3, x_24);
lean_inc(x_395);
lean_inc(x_382);
x_396 = l_Lean_Syntax_node1(x_382, x_390, x_395);
x_397 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_382);
lean_ctor_set_tag(x_279, 2);
lean_ctor_set(x_279, 1, x_397);
lean_ctor_set(x_279, 0, x_382);
x_398 = lean_mk_string_unchecked("Parser", 6, 6);
x_399 = lean_mk_string_unchecked("Term", 4, 4);
x_400 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_401 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_400);
x_402 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_403 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_402);
x_404 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_382);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_404);
lean_ctor_set(x_26, 0, x_382);
x_405 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_382);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_405);
lean_ctor_set(x_14, 0, x_382);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_26);
lean_inc(x_382);
x_406 = l_Lean_Syntax_node3(x_382, x_403, x_26, x_2, x_14);
x_407 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_382);
x_408 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_408, 0, x_382);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_409);
x_410 = l_String_toSubstring_x27(x_409);
x_411 = l_Lean_Name_mkStr1(x_409);
lean_inc(x_18);
lean_inc(x_19);
x_412 = l_Lean_addMacroScope(x_19, x_411, x_18);
lean_inc(x_382);
x_413 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_413, 0, x_382);
lean_ctor_set(x_413, 1, x_410);
lean_ctor_set(x_413, 2, x_412);
lean_ctor_set(x_413, 3, x_24);
lean_inc(x_382);
x_414 = l_Lean_Syntax_node3(x_382, x_401, x_406, x_408, x_413);
x_415 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_382);
x_416 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_416, 0, x_382);
lean_ctor_set(x_416, 1, x_415);
x_417 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_417);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_418 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_417);
lean_inc(x_382);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_382);
lean_ctor_set(x_419, 1, x_417);
x_420 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_421 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_420);
x_422 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_423 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_422);
x_424 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_424);
x_425 = l_String_toSubstring_x27(x_424);
x_426 = l_Lean_Name_mkStr1(x_424);
lean_inc(x_18);
lean_inc(x_19);
x_427 = l_Lean_addMacroScope(x_19, x_426, x_18);
lean_inc(x_382);
x_428 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_428, 0, x_382);
lean_ctor_set(x_428, 1, x_425);
lean_ctor_set(x_428, 2, x_427);
lean_ctor_set(x_428, 3, x_24);
x_429 = lean_mk_string_unchecked("null", 4, 4);
x_430 = l_Lean_Name_mkStr1(x_429);
x_431 = l_Array_mkArray0(lean_box(0));
lean_inc(x_430);
lean_inc(x_382);
x_432 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_432, 0, x_382);
lean_ctor_set(x_432, 1, x_430);
lean_ctor_set(x_432, 2, x_431);
x_433 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_382);
x_434 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_434, 0, x_382);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_388);
x_436 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_435);
x_437 = lean_mk_string_unchecked("Expr.appArg", 11, 11);
x_438 = l_String_toSubstring_x27(x_437);
x_439 = lean_mk_string_unchecked("Expr", 4, 4);
x_440 = lean_mk_string_unchecked("appArg", 6, 6);
lean_inc(x_440);
lean_inc(x_439);
x_441 = l_Lean_Name_mkStr2(x_439, x_440);
lean_inc(x_18);
lean_inc(x_19);
x_442 = l_Lean_addMacroScope(x_19, x_441, x_18);
lean_inc(x_439);
lean_inc(x_388);
x_443 = l_Lean_Name_mkStr3(x_388, x_439, x_440);
x_444 = lean_box(0);
lean_inc(x_443);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_443);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_24);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
lean_inc(x_382);
x_449 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_449, 0, x_382);
lean_ctor_set(x_449, 1, x_438);
lean_ctor_set(x_449, 2, x_442);
lean_ctor_set(x_449, 3, x_448);
lean_inc(x_2);
lean_inc(x_430);
lean_inc(x_382);
x_450 = l_Lean_Syntax_node2(x_382, x_430, x_2, x_395);
lean_inc(x_450);
lean_inc(x_436);
lean_inc(x_382);
x_451 = l_Lean_Syntax_node2(x_382, x_436, x_449, x_450);
lean_inc(x_434);
lean_inc_n(x_432, 2);
lean_inc(x_423);
lean_inc(x_382);
x_452 = l_Lean_Syntax_node5(x_382, x_423, x_428, x_432, x_432, x_434, x_451);
lean_inc(x_421);
lean_inc(x_382);
x_453 = l_Lean_Syntax_node1(x_382, x_421, x_452);
x_454 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_382);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_382);
lean_ctor_set(x_455, 1, x_454);
lean_inc(x_382);
x_456 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_456, 0, x_382);
lean_ctor_set(x_456, 1, x_21);
lean_ctor_set(x_456, 2, x_23);
lean_ctor_set(x_456, 3, x_24);
x_457 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_458 = l_String_toSubstring_x27(x_457);
x_459 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_459);
lean_inc(x_439);
x_460 = l_Lean_Name_mkStr2(x_439, x_459);
x_461 = l_Lean_addMacroScope(x_19, x_460, x_18);
lean_inc(x_388);
x_462 = l_Lean_Name_mkStr3(x_388, x_439, x_459);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_444);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_24);
lean_inc(x_382);
x_465 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_465, 0, x_382);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_461);
lean_ctor_set(x_465, 3, x_464);
lean_inc(x_436);
lean_inc(x_382);
x_466 = l_Lean_Syntax_node2(x_382, x_436, x_465, x_450);
lean_inc_n(x_432, 2);
lean_inc(x_382);
x_467 = l_Lean_Syntax_node5(x_382, x_423, x_456, x_432, x_432, x_434, x_466);
lean_inc(x_382);
x_468 = l_Lean_Syntax_node1(x_382, x_421, x_467);
lean_inc(x_455);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_382);
x_469 = l_Lean_Syntax_node4(x_382, x_418, x_419, x_468, x_455, x_277);
lean_inc(x_382);
x_470 = l_Lean_Syntax_node4(x_382, x_418, x_419, x_453, x_455, x_469);
x_471 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_382);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_382);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_mk_string_unchecked("tuple", 5, 5);
x_474 = l_Lean_Name_mkStr4(x_388, x_398, x_399, x_473);
lean_inc(x_382);
x_475 = l_Lean_Syntax_node3(x_382, x_474, x_26, x_432, x_14);
lean_inc(x_382);
x_476 = l_Lean_Syntax_node1(x_382, x_430, x_475);
lean_inc(x_382);
x_477 = l_Lean_Syntax_node2(x_382, x_436, x_1, x_476);
x_478 = l_Lean_Syntax_node8(x_382, x_385, x_387, x_396, x_279, x_414, x_416, x_470, x_472, x_477);
x_479 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_478, x_9, x_383);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_480 = lean_ctor_get(x_279, 0);
x_481 = lean_ctor_get(x_279, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_279);
x_482 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_12, x_480, x_9, x_481);
lean_dec(x_480);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_485 = x_482;
} else {
 lean_dec_ref(x_482);
 x_485 = lean_box(0);
}
x_486 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_487 = l_Lean_Name_mkStr1(x_486);
x_488 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_483);
if (lean_is_scalar(x_485)) {
 x_489 = lean_alloc_ctor(2, 2, 0);
} else {
 x_489 = x_485;
 lean_ctor_set_tag(x_489, 2);
}
lean_ctor_set(x_489, 0, x_483);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_mk_string_unchecked("Lean", 4, 4);
x_491 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_490);
x_492 = l_Lean_Name_mkStr2(x_490, x_491);
x_493 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_493);
x_494 = l_String_toSubstring_x27(x_493);
x_495 = l_Lean_Name_mkStr1(x_493);
lean_inc(x_18);
lean_inc(x_19);
x_496 = l_Lean_addMacroScope(x_19, x_495, x_18);
lean_inc(x_483);
x_497 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_497, 0, x_483);
lean_ctor_set(x_497, 1, x_494);
lean_ctor_set(x_497, 2, x_496);
lean_ctor_set(x_497, 3, x_24);
lean_inc(x_497);
lean_inc(x_483);
x_498 = l_Lean_Syntax_node1(x_483, x_492, x_497);
x_499 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_483);
x_500 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_500, 0, x_483);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_mk_string_unchecked("Parser", 6, 6);
x_502 = lean_mk_string_unchecked("Term", 4, 4);
x_503 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_504 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_503);
x_505 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_506 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_505);
x_507 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_483);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_507);
lean_ctor_set(x_26, 0, x_483);
x_508 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_483);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_508);
lean_ctor_set(x_14, 0, x_483);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_26);
lean_inc(x_483);
x_509 = l_Lean_Syntax_node3(x_483, x_506, x_26, x_2, x_14);
x_510 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_483);
x_511 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_511, 0, x_483);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_512);
x_513 = l_String_toSubstring_x27(x_512);
x_514 = l_Lean_Name_mkStr1(x_512);
lean_inc(x_18);
lean_inc(x_19);
x_515 = l_Lean_addMacroScope(x_19, x_514, x_18);
lean_inc(x_483);
x_516 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_516, 0, x_483);
lean_ctor_set(x_516, 1, x_513);
lean_ctor_set(x_516, 2, x_515);
lean_ctor_set(x_516, 3, x_24);
lean_inc(x_483);
x_517 = l_Lean_Syntax_node3(x_483, x_504, x_509, x_511, x_516);
x_518 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_483);
x_519 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_519, 0, x_483);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_520);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_521 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_520);
lean_inc(x_483);
x_522 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_522, 0, x_483);
lean_ctor_set(x_522, 1, x_520);
x_523 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_524 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_523);
x_525 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_526 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_525);
x_527 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_527);
x_528 = l_String_toSubstring_x27(x_527);
x_529 = l_Lean_Name_mkStr1(x_527);
lean_inc(x_18);
lean_inc(x_19);
x_530 = l_Lean_addMacroScope(x_19, x_529, x_18);
lean_inc(x_483);
x_531 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_531, 0, x_483);
lean_ctor_set(x_531, 1, x_528);
lean_ctor_set(x_531, 2, x_530);
lean_ctor_set(x_531, 3, x_24);
x_532 = lean_mk_string_unchecked("null", 4, 4);
x_533 = l_Lean_Name_mkStr1(x_532);
x_534 = l_Array_mkArray0(lean_box(0));
lean_inc(x_533);
lean_inc(x_483);
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_483);
lean_ctor_set(x_535, 1, x_533);
lean_ctor_set(x_535, 2, x_534);
x_536 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_483);
x_537 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_537, 0, x_483);
lean_ctor_set(x_537, 1, x_536);
x_538 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_490);
x_539 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_538);
x_540 = lean_mk_string_unchecked("Expr.appArg", 11, 11);
x_541 = l_String_toSubstring_x27(x_540);
x_542 = lean_mk_string_unchecked("Expr", 4, 4);
x_543 = lean_mk_string_unchecked("appArg", 6, 6);
lean_inc(x_543);
lean_inc(x_542);
x_544 = l_Lean_Name_mkStr2(x_542, x_543);
lean_inc(x_18);
lean_inc(x_19);
x_545 = l_Lean_addMacroScope(x_19, x_544, x_18);
lean_inc(x_542);
lean_inc(x_490);
x_546 = l_Lean_Name_mkStr3(x_490, x_542, x_543);
x_547 = lean_box(0);
lean_inc(x_546);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
x_549 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_549, 0, x_546);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_24);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_550);
lean_inc(x_483);
x_552 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_552, 0, x_483);
lean_ctor_set(x_552, 1, x_541);
lean_ctor_set(x_552, 2, x_545);
lean_ctor_set(x_552, 3, x_551);
lean_inc(x_2);
lean_inc(x_533);
lean_inc(x_483);
x_553 = l_Lean_Syntax_node2(x_483, x_533, x_2, x_497);
lean_inc(x_553);
lean_inc(x_539);
lean_inc(x_483);
x_554 = l_Lean_Syntax_node2(x_483, x_539, x_552, x_553);
lean_inc(x_537);
lean_inc_n(x_535, 2);
lean_inc(x_526);
lean_inc(x_483);
x_555 = l_Lean_Syntax_node5(x_483, x_526, x_531, x_535, x_535, x_537, x_554);
lean_inc(x_524);
lean_inc(x_483);
x_556 = l_Lean_Syntax_node1(x_483, x_524, x_555);
x_557 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_483);
x_558 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_558, 0, x_483);
lean_ctor_set(x_558, 1, x_557);
lean_inc(x_483);
x_559 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_559, 0, x_483);
lean_ctor_set(x_559, 1, x_21);
lean_ctor_set(x_559, 2, x_23);
lean_ctor_set(x_559, 3, x_24);
x_560 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_561 = l_String_toSubstring_x27(x_560);
x_562 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_562);
lean_inc(x_542);
x_563 = l_Lean_Name_mkStr2(x_542, x_562);
x_564 = l_Lean_addMacroScope(x_19, x_563, x_18);
lean_inc(x_490);
x_565 = l_Lean_Name_mkStr3(x_490, x_542, x_562);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_547);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_24);
lean_inc(x_483);
x_568 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_568, 0, x_483);
lean_ctor_set(x_568, 1, x_561);
lean_ctor_set(x_568, 2, x_564);
lean_ctor_set(x_568, 3, x_567);
lean_inc(x_539);
lean_inc(x_483);
x_569 = l_Lean_Syntax_node2(x_483, x_539, x_568, x_553);
lean_inc_n(x_535, 2);
lean_inc(x_483);
x_570 = l_Lean_Syntax_node5(x_483, x_526, x_559, x_535, x_535, x_537, x_569);
lean_inc(x_483);
x_571 = l_Lean_Syntax_node1(x_483, x_524, x_570);
lean_inc(x_558);
lean_inc(x_522);
lean_inc(x_521);
lean_inc(x_483);
x_572 = l_Lean_Syntax_node4(x_483, x_521, x_522, x_571, x_558, x_277);
lean_inc(x_483);
x_573 = l_Lean_Syntax_node4(x_483, x_521, x_522, x_556, x_558, x_572);
x_574 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_483);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_483);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_mk_string_unchecked("tuple", 5, 5);
x_577 = l_Lean_Name_mkStr4(x_490, x_501, x_502, x_576);
lean_inc(x_483);
x_578 = l_Lean_Syntax_node3(x_483, x_577, x_26, x_535, x_14);
lean_inc(x_483);
x_579 = l_Lean_Syntax_node1(x_483, x_533, x_578);
lean_inc(x_483);
x_580 = l_Lean_Syntax_node2(x_483, x_539, x_1, x_579);
x_581 = l_Lean_Syntax_node8(x_483, x_487, x_489, x_498, x_500, x_517, x_519, x_573, x_575, x_580);
x_582 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_581, x_9, x_484);
return x_582;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_583 = lean_ctor_get(x_26, 0);
x_584 = lean_ctor_get(x_26, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_26);
x_585 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_584);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
x_589 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_12, x_586, x_9, x_587);
lean_dec(x_586);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_592 = x_589;
} else {
 lean_dec_ref(x_589);
 x_592 = lean_box(0);
}
x_593 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_594 = l_Lean_Name_mkStr1(x_593);
x_595 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_590);
if (lean_is_scalar(x_592)) {
 x_596 = lean_alloc_ctor(2, 2, 0);
} else {
 x_596 = x_592;
 lean_ctor_set_tag(x_596, 2);
}
lean_ctor_set(x_596, 0, x_590);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_mk_string_unchecked("Lean", 4, 4);
x_598 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_597);
x_599 = l_Lean_Name_mkStr2(x_597, x_598);
x_600 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_600);
x_601 = l_String_toSubstring_x27(x_600);
x_602 = l_Lean_Name_mkStr1(x_600);
lean_inc(x_18);
lean_inc(x_19);
x_603 = l_Lean_addMacroScope(x_19, x_602, x_18);
lean_inc(x_590);
x_604 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_604, 0, x_590);
lean_ctor_set(x_604, 1, x_601);
lean_ctor_set(x_604, 2, x_603);
lean_ctor_set(x_604, 3, x_24);
lean_inc(x_604);
lean_inc(x_590);
x_605 = l_Lean_Syntax_node1(x_590, x_599, x_604);
x_606 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_590);
if (lean_is_scalar(x_588)) {
 x_607 = lean_alloc_ctor(2, 2, 0);
} else {
 x_607 = x_588;
 lean_ctor_set_tag(x_607, 2);
}
lean_ctor_set(x_607, 0, x_590);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_mk_string_unchecked("Parser", 6, 6);
x_609 = lean_mk_string_unchecked("Term", 4, 4);
x_610 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_611 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_610);
x_612 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_613 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_612);
x_614 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_590);
x_615 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_615, 0, x_590);
lean_ctor_set(x_615, 1, x_614);
x_616 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_590);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_616);
lean_ctor_set(x_14, 0, x_590);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_615);
lean_inc(x_590);
x_617 = l_Lean_Syntax_node3(x_590, x_613, x_615, x_2, x_14);
x_618 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_590);
x_619 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_619, 0, x_590);
lean_ctor_set(x_619, 1, x_618);
x_620 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_620);
x_621 = l_String_toSubstring_x27(x_620);
x_622 = l_Lean_Name_mkStr1(x_620);
lean_inc(x_18);
lean_inc(x_19);
x_623 = l_Lean_addMacroScope(x_19, x_622, x_18);
lean_inc(x_590);
x_624 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_624, 0, x_590);
lean_ctor_set(x_624, 1, x_621);
lean_ctor_set(x_624, 2, x_623);
lean_ctor_set(x_624, 3, x_24);
lean_inc(x_590);
x_625 = l_Lean_Syntax_node3(x_590, x_611, x_617, x_619, x_624);
x_626 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_590);
x_627 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_627, 0, x_590);
lean_ctor_set(x_627, 1, x_626);
x_628 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_628);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_629 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_628);
lean_inc(x_590);
x_630 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_630, 0, x_590);
lean_ctor_set(x_630, 1, x_628);
x_631 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_632 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_631);
x_633 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_634 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_633);
x_635 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_635);
x_636 = l_String_toSubstring_x27(x_635);
x_637 = l_Lean_Name_mkStr1(x_635);
lean_inc(x_18);
lean_inc(x_19);
x_638 = l_Lean_addMacroScope(x_19, x_637, x_18);
lean_inc(x_590);
x_639 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_639, 0, x_590);
lean_ctor_set(x_639, 1, x_636);
lean_ctor_set(x_639, 2, x_638);
lean_ctor_set(x_639, 3, x_24);
x_640 = lean_mk_string_unchecked("null", 4, 4);
x_641 = l_Lean_Name_mkStr1(x_640);
x_642 = l_Array_mkArray0(lean_box(0));
lean_inc(x_641);
lean_inc(x_590);
x_643 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_643, 0, x_590);
lean_ctor_set(x_643, 1, x_641);
lean_ctor_set(x_643, 2, x_642);
x_644 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_590);
x_645 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_645, 0, x_590);
lean_ctor_set(x_645, 1, x_644);
x_646 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_597);
x_647 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_646);
x_648 = lean_mk_string_unchecked("Expr.appArg", 11, 11);
x_649 = l_String_toSubstring_x27(x_648);
x_650 = lean_mk_string_unchecked("Expr", 4, 4);
x_651 = lean_mk_string_unchecked("appArg", 6, 6);
lean_inc(x_651);
lean_inc(x_650);
x_652 = l_Lean_Name_mkStr2(x_650, x_651);
lean_inc(x_18);
lean_inc(x_19);
x_653 = l_Lean_addMacroScope(x_19, x_652, x_18);
lean_inc(x_650);
lean_inc(x_597);
x_654 = l_Lean_Name_mkStr3(x_597, x_650, x_651);
x_655 = lean_box(0);
lean_inc(x_654);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_657, 0, x_654);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_24);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_656);
lean_ctor_set(x_659, 1, x_658);
lean_inc(x_590);
x_660 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_660, 0, x_590);
lean_ctor_set(x_660, 1, x_649);
lean_ctor_set(x_660, 2, x_653);
lean_ctor_set(x_660, 3, x_659);
lean_inc(x_2);
lean_inc(x_641);
lean_inc(x_590);
x_661 = l_Lean_Syntax_node2(x_590, x_641, x_2, x_604);
lean_inc(x_661);
lean_inc(x_647);
lean_inc(x_590);
x_662 = l_Lean_Syntax_node2(x_590, x_647, x_660, x_661);
lean_inc(x_645);
lean_inc_n(x_643, 2);
lean_inc(x_634);
lean_inc(x_590);
x_663 = l_Lean_Syntax_node5(x_590, x_634, x_639, x_643, x_643, x_645, x_662);
lean_inc(x_632);
lean_inc(x_590);
x_664 = l_Lean_Syntax_node1(x_590, x_632, x_663);
x_665 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_590);
x_666 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_666, 0, x_590);
lean_ctor_set(x_666, 1, x_665);
lean_inc(x_590);
x_667 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_667, 0, x_590);
lean_ctor_set(x_667, 1, x_21);
lean_ctor_set(x_667, 2, x_23);
lean_ctor_set(x_667, 3, x_24);
x_668 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_669 = l_String_toSubstring_x27(x_668);
x_670 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_670);
lean_inc(x_650);
x_671 = l_Lean_Name_mkStr2(x_650, x_670);
x_672 = l_Lean_addMacroScope(x_19, x_671, x_18);
lean_inc(x_597);
x_673 = l_Lean_Name_mkStr3(x_597, x_650, x_670);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_655);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_24);
lean_inc(x_590);
x_676 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_676, 0, x_590);
lean_ctor_set(x_676, 1, x_669);
lean_ctor_set(x_676, 2, x_672);
lean_ctor_set(x_676, 3, x_675);
lean_inc(x_647);
lean_inc(x_590);
x_677 = l_Lean_Syntax_node2(x_590, x_647, x_676, x_661);
lean_inc_n(x_643, 2);
lean_inc(x_590);
x_678 = l_Lean_Syntax_node5(x_590, x_634, x_667, x_643, x_643, x_645, x_677);
lean_inc(x_590);
x_679 = l_Lean_Syntax_node1(x_590, x_632, x_678);
lean_inc(x_666);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_590);
x_680 = l_Lean_Syntax_node4(x_590, x_629, x_630, x_679, x_666, x_583);
lean_inc(x_590);
x_681 = l_Lean_Syntax_node4(x_590, x_629, x_630, x_664, x_666, x_680);
x_682 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_590);
x_683 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_683, 0, x_590);
lean_ctor_set(x_683, 1, x_682);
x_684 = lean_mk_string_unchecked("tuple", 5, 5);
x_685 = l_Lean_Name_mkStr4(x_597, x_608, x_609, x_684);
lean_inc(x_590);
x_686 = l_Lean_Syntax_node3(x_590, x_685, x_615, x_643, x_14);
lean_inc(x_590);
x_687 = l_Lean_Syntax_node1(x_590, x_641, x_686);
lean_inc(x_590);
x_688 = l_Lean_Syntax_node2(x_590, x_647, x_1, x_687);
x_689 = l_Lean_Syntax_node8(x_590, x_594, x_596, x_605, x_607, x_625, x_627, x_681, x_683, x_688);
x_690 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_689, x_9, x_591);
return x_690;
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_691 = lean_ctor_get(x_14, 0);
x_692 = lean_ctor_get(x_14, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_14);
x_693 = lean_ctor_get(x_9, 2);
lean_inc(x_693);
x_694 = lean_ctor_get(x_9, 1);
lean_inc(x_694);
x_695 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_695);
x_696 = l_String_toSubstring_x27(x_695);
x_697 = l_Lean_Name_mkStr1(x_695);
lean_inc(x_693);
lean_inc(x_694);
x_698 = l_Lean_addMacroScope(x_694, x_697, x_693);
x_699 = lean_box(0);
lean_inc(x_698);
lean_inc(x_696);
x_700 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_700, 0, x_691);
lean_ctor_set(x_700, 1, x_696);
lean_ctor_set(x_700, 2, x_698);
lean_ctor_set(x_700, 3, x_699);
lean_inc(x_9);
lean_inc(x_1);
x_701 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_1, x_700, x_11, x_9, x_692);
if (x_7 == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
x_705 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_703);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_708 = x_705;
} else {
 lean_dec_ref(x_705);
 x_708 = lean_box(0);
}
x_709 = l_Lean_SourceInfo_fromRef(x_706, x_12);
lean_dec(x_706);
x_710 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_711 = l_Lean_Name_mkStr1(x_710);
x_712 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_709);
if (lean_is_scalar(x_708)) {
 x_713 = lean_alloc_ctor(2, 2, 0);
} else {
 x_713 = x_708;
 lean_ctor_set_tag(x_713, 2);
}
lean_ctor_set(x_713, 0, x_709);
lean_ctor_set(x_713, 1, x_712);
x_714 = lean_mk_string_unchecked("Lean", 4, 4);
x_715 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_714);
x_716 = l_Lean_Name_mkStr2(x_714, x_715);
x_717 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_717);
x_718 = l_String_toSubstring_x27(x_717);
x_719 = l_Lean_Name_mkStr1(x_717);
lean_inc(x_693);
lean_inc(x_694);
x_720 = l_Lean_addMacroScope(x_694, x_719, x_693);
lean_inc(x_709);
x_721 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_721, 0, x_709);
lean_ctor_set(x_721, 1, x_718);
lean_ctor_set(x_721, 2, x_720);
lean_ctor_set(x_721, 3, x_699);
lean_inc(x_721);
lean_inc(x_709);
x_722 = l_Lean_Syntax_node1(x_709, x_716, x_721);
x_723 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_709);
if (lean_is_scalar(x_704)) {
 x_724 = lean_alloc_ctor(2, 2, 0);
} else {
 x_724 = x_704;
 lean_ctor_set_tag(x_724, 2);
}
lean_ctor_set(x_724, 0, x_709);
lean_ctor_set(x_724, 1, x_723);
x_725 = lean_mk_string_unchecked("Parser", 6, 6);
x_726 = lean_mk_string_unchecked("Term", 4, 4);
x_727 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_728 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_727);
x_729 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_730 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_729);
x_731 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_709);
x_732 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_732, 0, x_709);
lean_ctor_set(x_732, 1, x_731);
x_733 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_709);
x_734 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_734, 0, x_709);
lean_ctor_set(x_734, 1, x_733);
lean_inc(x_734);
lean_inc(x_2);
lean_inc(x_732);
lean_inc(x_709);
x_735 = l_Lean_Syntax_node3(x_709, x_730, x_732, x_2, x_734);
x_736 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_709);
x_737 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_737, 0, x_709);
lean_ctor_set(x_737, 1, x_736);
x_738 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_738);
x_739 = l_String_toSubstring_x27(x_738);
x_740 = l_Lean_Name_mkStr1(x_738);
lean_inc(x_693);
lean_inc(x_694);
x_741 = l_Lean_addMacroScope(x_694, x_740, x_693);
lean_inc(x_709);
x_742 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_742, 0, x_709);
lean_ctor_set(x_742, 1, x_739);
lean_ctor_set(x_742, 2, x_741);
lean_ctor_set(x_742, 3, x_699);
lean_inc(x_709);
x_743 = l_Lean_Syntax_node3(x_709, x_728, x_735, x_737, x_742);
x_744 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_709);
x_745 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_745, 0, x_709);
lean_ctor_set(x_745, 1, x_744);
x_746 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_746);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_747 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_746);
lean_inc(x_709);
x_748 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_748, 0, x_709);
lean_ctor_set(x_748, 1, x_746);
x_749 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_750 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_749);
x_751 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_752 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_751);
lean_inc(x_709);
x_753 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_753, 0, x_709);
lean_ctor_set(x_753, 1, x_696);
lean_ctor_set(x_753, 2, x_698);
lean_ctor_set(x_753, 3, x_699);
x_754 = lean_mk_string_unchecked("null", 4, 4);
x_755 = l_Lean_Name_mkStr1(x_754);
x_756 = l_Array_mkArray0(lean_box(0));
lean_inc(x_755);
lean_inc(x_709);
x_757 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_757, 0, x_709);
lean_ctor_set(x_757, 1, x_755);
lean_ctor_set(x_757, 2, x_756);
x_758 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_709);
x_759 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_759, 0, x_709);
lean_ctor_set(x_759, 1, x_758);
x_760 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_714);
x_761 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_760);
x_762 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_763 = l_String_toSubstring_x27(x_762);
x_764 = lean_mk_string_unchecked("Expr", 4, 4);
x_765 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_765);
lean_inc(x_764);
x_766 = l_Lean_Name_mkStr2(x_764, x_765);
x_767 = l_Lean_addMacroScope(x_694, x_766, x_693);
lean_inc(x_714);
x_768 = l_Lean_Name_mkStr3(x_714, x_764, x_765);
x_769 = lean_box(0);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
x_771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_699);
lean_inc(x_709);
x_772 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_772, 0, x_709);
lean_ctor_set(x_772, 1, x_763);
lean_ctor_set(x_772, 2, x_767);
lean_ctor_set(x_772, 3, x_771);
lean_inc(x_2);
lean_inc(x_755);
lean_inc(x_709);
x_773 = l_Lean_Syntax_node2(x_709, x_755, x_2, x_721);
lean_inc(x_761);
lean_inc(x_709);
x_774 = l_Lean_Syntax_node2(x_709, x_761, x_772, x_773);
lean_inc_n(x_757, 2);
lean_inc(x_709);
x_775 = l_Lean_Syntax_node5(x_709, x_752, x_753, x_757, x_757, x_759, x_774);
lean_inc(x_709);
x_776 = l_Lean_Syntax_node1(x_709, x_750, x_775);
x_777 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_709);
x_778 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_778, 0, x_709);
lean_ctor_set(x_778, 1, x_777);
lean_inc(x_709);
x_779 = l_Lean_Syntax_node4(x_709, x_747, x_748, x_776, x_778, x_702);
x_780 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_709);
x_781 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_781, 0, x_709);
lean_ctor_set(x_781, 1, x_780);
x_782 = lean_mk_string_unchecked("tuple", 5, 5);
x_783 = l_Lean_Name_mkStr4(x_714, x_725, x_726, x_782);
lean_inc(x_709);
x_784 = l_Lean_Syntax_node3(x_709, x_783, x_732, x_757, x_734);
lean_inc(x_709);
x_785 = l_Lean_Syntax_node1(x_709, x_755, x_784);
lean_inc(x_709);
x_786 = l_Lean_Syntax_node2(x_709, x_761, x_1, x_785);
x_787 = l_Lean_Syntax_node8(x_709, x_711, x_713, x_722, x_724, x_743, x_745, x_779, x_781, x_786);
x_788 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_787, x_9, x_707);
return x_788;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_789 = lean_ctor_get(x_701, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_701, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_791 = x_701;
} else {
 lean_dec_ref(x_701);
 x_791 = lean_box(0);
}
x_792 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_9, x_9, x_790);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_795 = x_792;
} else {
 lean_dec_ref(x_792);
 x_795 = lean_box(0);
}
x_796 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_12, x_793, x_9, x_794);
lean_dec(x_793);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_799 = x_796;
} else {
 lean_dec_ref(x_796);
 x_799 = lean_box(0);
}
x_800 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_801 = l_Lean_Name_mkStr1(x_800);
x_802 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_797);
if (lean_is_scalar(x_799)) {
 x_803 = lean_alloc_ctor(2, 2, 0);
} else {
 x_803 = x_799;
 lean_ctor_set_tag(x_803, 2);
}
lean_ctor_set(x_803, 0, x_797);
lean_ctor_set(x_803, 1, x_802);
x_804 = lean_mk_string_unchecked("Lean", 4, 4);
x_805 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_804);
x_806 = l_Lean_Name_mkStr2(x_804, x_805);
x_807 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_807);
x_808 = l_String_toSubstring_x27(x_807);
x_809 = l_Lean_Name_mkStr1(x_807);
lean_inc(x_693);
lean_inc(x_694);
x_810 = l_Lean_addMacroScope(x_694, x_809, x_693);
lean_inc(x_797);
x_811 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_811, 0, x_797);
lean_ctor_set(x_811, 1, x_808);
lean_ctor_set(x_811, 2, x_810);
lean_ctor_set(x_811, 3, x_699);
lean_inc(x_811);
lean_inc(x_797);
x_812 = l_Lean_Syntax_node1(x_797, x_806, x_811);
x_813 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_797);
if (lean_is_scalar(x_795)) {
 x_814 = lean_alloc_ctor(2, 2, 0);
} else {
 x_814 = x_795;
 lean_ctor_set_tag(x_814, 2);
}
lean_ctor_set(x_814, 0, x_797);
lean_ctor_set(x_814, 1, x_813);
x_815 = lean_mk_string_unchecked("Parser", 6, 6);
x_816 = lean_mk_string_unchecked("Term", 4, 4);
x_817 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_818 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_817);
x_819 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_820 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_819);
x_821 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_797);
if (lean_is_scalar(x_791)) {
 x_822 = lean_alloc_ctor(2, 2, 0);
} else {
 x_822 = x_791;
 lean_ctor_set_tag(x_822, 2);
}
lean_ctor_set(x_822, 0, x_797);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_797);
x_824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_824, 0, x_797);
lean_ctor_set(x_824, 1, x_823);
lean_inc(x_824);
lean_inc(x_2);
lean_inc(x_822);
lean_inc(x_797);
x_825 = l_Lean_Syntax_node3(x_797, x_820, x_822, x_2, x_824);
x_826 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_797);
x_827 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_827, 0, x_797);
lean_ctor_set(x_827, 1, x_826);
x_828 = lean_mk_string_unchecked("isApp", 5, 5);
lean_inc(x_828);
x_829 = l_String_toSubstring_x27(x_828);
x_830 = l_Lean_Name_mkStr1(x_828);
lean_inc(x_693);
lean_inc(x_694);
x_831 = l_Lean_addMacroScope(x_694, x_830, x_693);
lean_inc(x_797);
x_832 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_832, 0, x_797);
lean_ctor_set(x_832, 1, x_829);
lean_ctor_set(x_832, 2, x_831);
lean_ctor_set(x_832, 3, x_699);
lean_inc(x_797);
x_833 = l_Lean_Syntax_node3(x_797, x_818, x_825, x_827, x_832);
x_834 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_797);
x_835 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_835, 0, x_797);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_836);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_837 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_836);
lean_inc(x_797);
x_838 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_838, 0, x_797);
lean_ctor_set(x_838, 1, x_836);
x_839 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_840 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_839);
x_841 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_842 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_841);
x_843 = lean_mk_string_unchecked("a", 1, 1);
lean_inc(x_843);
x_844 = l_String_toSubstring_x27(x_843);
x_845 = l_Lean_Name_mkStr1(x_843);
lean_inc(x_693);
lean_inc(x_694);
x_846 = l_Lean_addMacroScope(x_694, x_845, x_693);
lean_inc(x_797);
x_847 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_847, 0, x_797);
lean_ctor_set(x_847, 1, x_844);
lean_ctor_set(x_847, 2, x_846);
lean_ctor_set(x_847, 3, x_699);
x_848 = lean_mk_string_unchecked("null", 4, 4);
x_849 = l_Lean_Name_mkStr1(x_848);
x_850 = l_Array_mkArray0(lean_box(0));
lean_inc(x_849);
lean_inc(x_797);
x_851 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_851, 0, x_797);
lean_ctor_set(x_851, 1, x_849);
lean_ctor_set(x_851, 2, x_850);
x_852 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_797);
x_853 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_853, 0, x_797);
lean_ctor_set(x_853, 1, x_852);
x_854 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_804);
x_855 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_854);
x_856 = lean_mk_string_unchecked("Expr.appArg", 11, 11);
x_857 = l_String_toSubstring_x27(x_856);
x_858 = lean_mk_string_unchecked("Expr", 4, 4);
x_859 = lean_mk_string_unchecked("appArg", 6, 6);
lean_inc(x_859);
lean_inc(x_858);
x_860 = l_Lean_Name_mkStr2(x_858, x_859);
lean_inc(x_693);
lean_inc(x_694);
x_861 = l_Lean_addMacroScope(x_694, x_860, x_693);
lean_inc(x_858);
lean_inc(x_804);
x_862 = l_Lean_Name_mkStr3(x_804, x_858, x_859);
x_863 = lean_box(0);
lean_inc(x_862);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
x_865 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_865, 0, x_862);
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_699);
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_866);
lean_inc(x_797);
x_868 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_868, 0, x_797);
lean_ctor_set(x_868, 1, x_857);
lean_ctor_set(x_868, 2, x_861);
lean_ctor_set(x_868, 3, x_867);
lean_inc(x_2);
lean_inc(x_849);
lean_inc(x_797);
x_869 = l_Lean_Syntax_node2(x_797, x_849, x_2, x_811);
lean_inc(x_869);
lean_inc(x_855);
lean_inc(x_797);
x_870 = l_Lean_Syntax_node2(x_797, x_855, x_868, x_869);
lean_inc(x_853);
lean_inc_n(x_851, 2);
lean_inc(x_842);
lean_inc(x_797);
x_871 = l_Lean_Syntax_node5(x_797, x_842, x_847, x_851, x_851, x_853, x_870);
lean_inc(x_840);
lean_inc(x_797);
x_872 = l_Lean_Syntax_node1(x_797, x_840, x_871);
x_873 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_797);
x_874 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_874, 0, x_797);
lean_ctor_set(x_874, 1, x_873);
lean_inc(x_797);
x_875 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_875, 0, x_797);
lean_ctor_set(x_875, 1, x_696);
lean_ctor_set(x_875, 2, x_698);
lean_ctor_set(x_875, 3, x_699);
x_876 = lean_mk_string_unchecked("Expr.appFnCleanup", 17, 17);
x_877 = l_String_toSubstring_x27(x_876);
x_878 = lean_mk_string_unchecked("appFnCleanup", 12, 12);
lean_inc(x_878);
lean_inc(x_858);
x_879 = l_Lean_Name_mkStr2(x_858, x_878);
x_880 = l_Lean_addMacroScope(x_694, x_879, x_693);
lean_inc(x_804);
x_881 = l_Lean_Name_mkStr3(x_804, x_858, x_878);
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_863);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_699);
lean_inc(x_797);
x_884 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_884, 0, x_797);
lean_ctor_set(x_884, 1, x_877);
lean_ctor_set(x_884, 2, x_880);
lean_ctor_set(x_884, 3, x_883);
lean_inc(x_855);
lean_inc(x_797);
x_885 = l_Lean_Syntax_node2(x_797, x_855, x_884, x_869);
lean_inc_n(x_851, 2);
lean_inc(x_797);
x_886 = l_Lean_Syntax_node5(x_797, x_842, x_875, x_851, x_851, x_853, x_885);
lean_inc(x_797);
x_887 = l_Lean_Syntax_node1(x_797, x_840, x_886);
lean_inc(x_874);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_797);
x_888 = l_Lean_Syntax_node4(x_797, x_837, x_838, x_887, x_874, x_789);
lean_inc(x_797);
x_889 = l_Lean_Syntax_node4(x_797, x_837, x_838, x_872, x_874, x_888);
x_890 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_797);
x_891 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_891, 0, x_797);
lean_ctor_set(x_891, 1, x_890);
x_892 = lean_mk_string_unchecked("tuple", 5, 5);
x_893 = l_Lean_Name_mkStr4(x_804, x_815, x_816, x_892);
lean_inc(x_797);
x_894 = l_Lean_Syntax_node3(x_797, x_893, x_822, x_851, x_824);
lean_inc(x_797);
x_895 = l_Lean_Syntax_node1(x_797, x_849, x_894);
lean_inc(x_797);
x_896 = l_Lean_Syntax_node2(x_797, x_855, x_1, x_895);
x_897 = l_Lean_Syntax_node8(x_797, x_801, x_803, x_812, x_814, x_833, x_835, x_889, x_891, x_896);
x_898 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_897, x_9, x_798);
return x_898;
}
}
}
else
{
lean_object* x_899; lean_object* x_900; uint8_t x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_11);
x_899 = lean_ctor_get(x_9, 5);
lean_inc(x_899);
x_900 = lean_box(0);
x_901 = lean_unbox(x_900);
x_902 = l_Lean_SourceInfo_fromRef(x_899, x_901);
lean_dec(x_899);
x_903 = lean_mk_string_unchecked("Lean", 4, 4);
x_904 = lean_mk_string_unchecked("Parser", 6, 6);
x_905 = lean_mk_string_unchecked("Term", 4, 4);
x_906 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_905);
lean_inc(x_904);
lean_inc(x_903);
x_907 = l_Lean_Name_mkStr4(x_903, x_904, x_905, x_906);
x_908 = lean_mk_string_unchecked("null", 4, 4);
x_909 = l_Lean_Name_mkStr1(x_908);
x_910 = lean_mk_string_unchecked("tuple", 5, 5);
x_911 = l_Lean_Name_mkStr4(x_903, x_904, x_905, x_910);
x_912 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_902);
x_913 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_913, 0, x_902);
lean_ctor_set(x_913, 1, x_912);
x_914 = l_Array_mkArray0(lean_box(0));
lean_inc(x_909);
lean_inc(x_902);
x_915 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_915, 0, x_902);
lean_ctor_set(x_915, 1, x_909);
lean_ctor_set(x_915, 2, x_914);
x_916 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_902);
x_917 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_917, 0, x_902);
lean_ctor_set(x_917, 1, x_916);
lean_inc(x_902);
x_918 = l_Lean_Syntax_node3(x_902, x_911, x_913, x_915, x_917);
lean_inc(x_902);
x_919 = l_Lean_Syntax_node1(x_902, x_909, x_918);
x_920 = l_Lean_Syntax_node2(x_902, x_907, x_1, x_919);
x_921 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(x_3, x_2, x_6, x_920, x_9, x_10);
return x_921;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_MatchExpr_generate_loop___lam__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_MatchExpr_initK(x_8, x_3, x_4);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_12;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_3);
x_16 = l_Lean_Elab_Term_MatchExpr_initK(x_14, x_3, x_4);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
x_1 = x_15;
x_2 = x_19;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_7);
x_9 = l_Lean_Elab_Term_MatchExpr_getParams(x_7, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_SourceInfo_fromRef(x_13, x_15);
lean_dec(x_13);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
lean_inc(x_16);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_16);
x_22 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_23 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_22);
x_24 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_25 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_24);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_mk_string_unchecked("null", 4, 4);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Array_mkArray0(lean_box(0));
lean_inc(x_29);
x_30 = l_Array_append(lean_box(0), x_29, x_11);
lean_dec(x_11);
lean_inc(x_28);
lean_inc(x_16);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
lean_inc(x_16);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_16);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_1, 0, x_16);
x_34 = lean_ctor_get(x_7, 3);
lean_inc(x_34);
lean_dec(x_7);
lean_inc(x_16);
x_35 = l_Lean_Syntax_node5(x_16, x_25, x_26, x_31, x_32, x_1, x_34);
lean_inc(x_16);
x_36 = l_Lean_Syntax_node1(x_16, x_23, x_35);
x_37 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_16);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_node4(x_16, x_21, x_9, x_36, x_38, x_2);
x_1 = x_8;
x_2 = x_39;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_ctor_get(x_3, 5);
lean_inc(x_43);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_SourceInfo_fromRef(x_43, x_45);
lean_dec(x_43);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Term", 4, 4);
x_50 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_51 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_50);
lean_inc(x_46);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_54 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_53);
x_55 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_56 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_55);
x_57 = lean_ctor_get(x_7, 4);
lean_inc(x_57);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = l_Array_mkArray0(lean_box(0));
lean_inc(x_60);
x_61 = l_Array_append(lean_box(0), x_60, x_41);
lean_dec(x_41);
lean_inc(x_59);
lean_inc(x_46);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_61);
lean_inc(x_46);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
x_64 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_46);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_46);
x_65 = lean_ctor_get(x_7, 3);
lean_inc(x_65);
lean_dec(x_7);
lean_inc(x_46);
x_66 = l_Lean_Syntax_node5(x_46, x_56, x_57, x_62, x_63, x_1, x_65);
lean_inc(x_46);
x_67 = l_Lean_Syntax_node1(x_46, x_54, x_66);
x_68 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_46);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_46);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Syntax_node4(x_46, x_51, x_52, x_67, x_69, x_2);
x_1 = x_8;
x_2 = x_70;
x_4 = x_42;
goto _start;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_72);
x_74 = l_Lean_Elab_Term_MatchExpr_getParams(x_72, x_3, x_4);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_3, 5);
lean_inc(x_78);
x_79 = lean_box(0);
x_80 = lean_unbox(x_79);
x_81 = l_Lean_SourceInfo_fromRef(x_78, x_80);
lean_dec(x_78);
x_82 = lean_mk_string_unchecked("Lean", 4, 4);
x_83 = lean_mk_string_unchecked("Parser", 6, 6);
x_84 = lean_mk_string_unchecked("Term", 4, 4);
x_85 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_86 = l_Lean_Name_mkStr4(x_82, x_83, x_84, x_85);
lean_inc(x_81);
if (lean_is_scalar(x_77)) {
 x_87 = lean_alloc_ctor(2, 2, 0);
} else {
 x_87 = x_77;
 lean_ctor_set_tag(x_87, 2);
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_89 = l_Lean_Name_mkStr4(x_82, x_83, x_84, x_88);
x_90 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_91 = l_Lean_Name_mkStr4(x_82, x_83, x_84, x_90);
x_92 = lean_ctor_get(x_72, 4);
lean_inc(x_92);
x_93 = lean_mk_string_unchecked("null", 4, 4);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = l_Array_mkArray0(lean_box(0));
lean_inc(x_95);
x_96 = l_Array_append(lean_box(0), x_95, x_75);
lean_dec(x_75);
lean_inc(x_94);
lean_inc(x_81);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_81);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_81);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_95);
x_99 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_81);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_81);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_ctor_get(x_72, 3);
lean_inc(x_101);
lean_dec(x_72);
lean_inc(x_81);
x_102 = l_Lean_Syntax_node5(x_81, x_91, x_92, x_97, x_98, x_100, x_101);
lean_inc(x_81);
x_103 = l_Lean_Syntax_node1(x_81, x_89, x_102);
x_104 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_81);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_81);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Syntax_node4(x_81, x_86, x_87, x_103, x_105, x_2);
x_1 = x_73;
x_2 = x_106;
x_4 = x_76;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_8);
x_10 = l_Lean_Elab_Term_MatchExpr_getParams(x_8, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
lean_inc(x_17);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_17);
x_23 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_24 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_23);
x_25 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_26 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_25);
x_27 = lean_ctor_get(x_8, 4);
lean_inc(x_27);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Array_mkArray0(lean_box(0));
lean_inc(x_30);
x_31 = l_Array_append(lean_box(0), x_30, x_12);
lean_dec(x_12);
lean_inc(x_29);
lean_inc(x_17);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_17);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_17);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 1, x_34);
lean_ctor_set(x_2, 0, x_17);
x_35 = lean_ctor_get(x_8, 3);
lean_inc(x_35);
lean_dec(x_8);
lean_inc(x_17);
x_36 = l_Lean_Syntax_node5(x_17, x_26, x_27, x_32, x_33, x_2, x_35);
lean_inc(x_17);
x_37 = l_Lean_Syntax_node1(x_17, x_24, x_36);
x_38 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_17);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Syntax_node4(x_17, x_22, x_10, x_37, x_39, x_3);
x_41 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(x_9, x_40, x_4, x_13);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_ctor_get(x_4, 5);
lean_inc(x_44);
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_47 = l_Lean_SourceInfo_fromRef(x_44, x_46);
lean_dec(x_44);
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_mk_string_unchecked("Parser", 6, 6);
x_50 = lean_mk_string_unchecked("Term", 4, 4);
x_51 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
lean_inc(x_47);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_55 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_54);
x_56 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_57 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_56);
x_58 = lean_ctor_get(x_8, 4);
lean_inc(x_58);
x_59 = lean_mk_string_unchecked("null", 4, 4);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = l_Array_mkArray0(lean_box(0));
lean_inc(x_61);
x_62 = l_Array_append(lean_box(0), x_61, x_42);
lean_dec(x_42);
lean_inc(x_60);
lean_inc(x_47);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_47);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
lean_inc(x_47);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
x_65 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_47);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_47);
x_66 = lean_ctor_get(x_8, 3);
lean_inc(x_66);
lean_dec(x_8);
lean_inc(x_47);
x_67 = l_Lean_Syntax_node5(x_47, x_57, x_58, x_63, x_64, x_2, x_66);
lean_inc(x_47);
x_68 = l_Lean_Syntax_node1(x_47, x_55, x_67);
x_69 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_47);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Syntax_node4(x_47, x_52, x_53, x_68, x_70, x_3);
x_72 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(x_9, x_71, x_4, x_43);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_73);
x_75 = l_Lean_Elab_Term_MatchExpr_getParams(x_73, x_4, x_5);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_4, 5);
lean_inc(x_79);
x_80 = lean_box(0);
x_81 = lean_unbox(x_80);
x_82 = l_Lean_SourceInfo_fromRef(x_79, x_81);
lean_dec(x_79);
x_83 = lean_mk_string_unchecked("Lean", 4, 4);
x_84 = lean_mk_string_unchecked("Parser", 6, 6);
x_85 = lean_mk_string_unchecked("Term", 4, 4);
x_86 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_87 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_86);
lean_inc(x_82);
if (lean_is_scalar(x_78)) {
 x_88 = lean_alloc_ctor(2, 2, 0);
} else {
 x_88 = x_78;
 lean_ctor_set_tag(x_88, 2);
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_90 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_89);
x_91 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_92 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_91);
x_93 = lean_ctor_get(x_73, 4);
lean_inc(x_93);
x_94 = lean_mk_string_unchecked("null", 4, 4);
x_95 = l_Lean_Name_mkStr1(x_94);
x_96 = l_Array_mkArray0(lean_box(0));
lean_inc(x_96);
x_97 = l_Array_append(lean_box(0), x_96, x_76);
lean_dec(x_76);
lean_inc(x_95);
lean_inc(x_82);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_97);
lean_inc(x_82);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_82);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
x_100 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_82);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_ctor_get(x_73, 3);
lean_inc(x_102);
lean_dec(x_73);
lean_inc(x_82);
x_103 = l_Lean_Syntax_node5(x_82, x_92, x_93, x_98, x_99, x_101, x_102);
lean_inc(x_82);
x_104 = l_Lean_Syntax_node1(x_82, x_90, x_103);
x_105 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_82);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Syntax_node4(x_82, x_87, x_88, x_104, x_106, x_3);
x_108 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___redArg(x_74, x_107, x_4, x_77);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_SourceInfo_fromRef(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(0);
lean_inc(x_4);
x_7 = l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__0(x_2, x_6, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_13, x_4, x_14);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_21, x_4, x_22);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_27);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
x_31 = l_String_toSubstring_x27(x_27);
lean_inc(x_29);
lean_inc(x_30);
x_32 = l_Lean_addMacroScope(x_30, x_28, x_29);
x_33 = lean_box(0);
lean_inc(x_32);
lean_inc(x_31);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_35);
x_36 = l_String_toSubstring_x27(x_35);
x_37 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_29);
lean_inc(x_30);
x_38 = l_Lean_addMacroScope(x_30, x_37, x_29);
lean_inc(x_38);
lean_inc(x_36);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_33);
lean_inc(x_4);
lean_inc(x_9);
x_40 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_39, x_34, x_9, x_4, x_26);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_46, x_4, x_47);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_mk_string_unchecked("Lean", 4, 4);
x_53 = lean_mk_string_unchecked("Parser", 6, 6);
x_54 = lean_mk_string_unchecked("Term", 4, 4);
x_55 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_55);
lean_inc(x_50);
lean_ctor_set_tag(x_48, 2);
lean_ctor_set(x_48, 1, x_55);
x_57 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_58 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_57);
x_59 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_60 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_59);
lean_inc(x_50);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_36);
lean_ctor_set(x_61, 2, x_38);
lean_ctor_set(x_61, 3, x_33);
x_62 = lean_mk_string_unchecked("null", 4, 4);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_65 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_64);
x_66 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_50);
lean_ctor_set_tag(x_44, 2);
lean_ctor_set(x_44, 1, x_66);
lean_ctor_set(x_44, 0, x_50);
x_67 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_68 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_67);
x_69 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_50);
lean_ctor_set_tag(x_40, 2);
lean_ctor_set(x_40, 1, x_69);
lean_ctor_set(x_40, 0, x_50);
lean_inc(x_50);
x_70 = l_Lean_Syntax_node1(x_50, x_68, x_40);
lean_inc(x_63);
lean_inc(x_50);
x_71 = l_Lean_Syntax_node1(x_50, x_63, x_70);
x_72 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_50);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_72);
lean_ctor_set(x_23, 0, x_50);
x_73 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_73);
x_74 = l_String_toSubstring_x27(x_73);
x_75 = l_Lean_Name_mkStr1(x_73);
lean_inc(x_29);
lean_inc(x_75);
lean_inc(x_30);
x_76 = l_Lean_addMacroScope(x_30, x_75, x_29);
x_77 = lean_box(0);
lean_inc(x_75);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_77);
lean_ctor_set(x_19, 0, x_75);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_78);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_inc(x_50);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_50);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_11);
lean_inc(x_63);
lean_inc(x_50);
x_80 = l_Lean_Syntax_node2(x_50, x_63, x_23, x_79);
x_81 = l_Array_mkArray0(lean_box(0));
lean_inc(x_63);
lean_inc(x_50);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_50);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_50);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_83);
lean_ctor_set(x_7, 0, x_50);
lean_inc(x_82);
lean_inc(x_50);
x_84 = l_Lean_Syntax_node5(x_50, x_65, x_44, x_71, x_80, x_82, x_7);
lean_inc(x_63);
lean_inc(x_50);
x_85 = l_Lean_Syntax_node1(x_50, x_63, x_84);
x_86 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_50);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_50);
lean_ctor_set(x_87, 1, x_86);
lean_inc(x_87);
lean_inc(x_82);
lean_inc(x_60);
lean_inc(x_50);
x_88 = l_Lean_Syntax_node5(x_50, x_60, x_61, x_85, x_82, x_87, x_3);
lean_inc(x_58);
lean_inc(x_50);
x_89 = l_Lean_Syntax_node1(x_50, x_58, x_88);
x_90 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_50);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_50);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_92);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_93 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_92);
lean_inc(x_50);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_50);
lean_ctor_set(x_94, 1, x_92);
lean_inc(x_50);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_50);
lean_ctor_set(x_95, 1, x_31);
lean_ctor_set(x_95, 2, x_32);
lean_ctor_set(x_95, 3, x_33);
x_96 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_52);
x_97 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_96);
x_98 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_99 = l_String_toSubstring_x27(x_98);
x_100 = lean_mk_string_unchecked("Expr", 4, 4);
x_101 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_101);
lean_inc(x_100);
x_102 = l_Lean_Name_mkStr2(x_100, x_101);
x_103 = l_Lean_addMacroScope(x_30, x_102, x_29);
x_104 = l_Lean_Name_mkStr3(x_52, x_100, x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_77);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_33);
lean_inc(x_50);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_50);
lean_ctor_set(x_107, 1, x_99);
lean_ctor_set(x_107, 2, x_103);
lean_ctor_set(x_107, 3, x_106);
lean_inc(x_50);
x_108 = l_Lean_Syntax_node1(x_50, x_63, x_1);
lean_inc(x_50);
x_109 = l_Lean_Syntax_node2(x_50, x_97, x_107, x_108);
lean_inc(x_82);
lean_inc(x_50);
x_110 = l_Lean_Syntax_node5(x_50, x_60, x_95, x_82, x_82, x_87, x_109);
lean_inc(x_50);
x_111 = l_Lean_Syntax_node1(x_50, x_58, x_110);
lean_inc(x_91);
lean_inc(x_50);
x_112 = l_Lean_Syntax_node4(x_50, x_93, x_94, x_111, x_91, x_42);
x_113 = l_Lean_Syntax_node4(x_50, x_56, x_48, x_89, x_91, x_112);
lean_inc(x_9);
x_114 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_113, x_4, x_51);
lean_dec(x_9);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_114);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_119 = lean_ctor_get(x_48, 0);
x_120 = lean_ctor_get(x_48, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_48);
x_121 = lean_mk_string_unchecked("Lean", 4, 4);
x_122 = lean_mk_string_unchecked("Parser", 6, 6);
x_123 = lean_mk_string_unchecked("Term", 4, 4);
x_124 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_125 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_124);
lean_inc(x_119);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_128 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_127);
x_129 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_130 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_129);
lean_inc(x_119);
x_131 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_131, 0, x_119);
lean_ctor_set(x_131, 1, x_36);
lean_ctor_set(x_131, 2, x_38);
lean_ctor_set(x_131, 3, x_33);
x_132 = lean_mk_string_unchecked("null", 4, 4);
x_133 = l_Lean_Name_mkStr1(x_132);
x_134 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_135 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_134);
x_136 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_119);
lean_ctor_set_tag(x_44, 2);
lean_ctor_set(x_44, 1, x_136);
lean_ctor_set(x_44, 0, x_119);
x_137 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_138 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_137);
x_139 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_119);
lean_ctor_set_tag(x_40, 2);
lean_ctor_set(x_40, 1, x_139);
lean_ctor_set(x_40, 0, x_119);
lean_inc(x_119);
x_140 = l_Lean_Syntax_node1(x_119, x_138, x_40);
lean_inc(x_133);
lean_inc(x_119);
x_141 = l_Lean_Syntax_node1(x_119, x_133, x_140);
x_142 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_119);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_142);
lean_ctor_set(x_23, 0, x_119);
x_143 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_143);
x_144 = l_String_toSubstring_x27(x_143);
x_145 = l_Lean_Name_mkStr1(x_143);
lean_inc(x_29);
lean_inc(x_145);
lean_inc(x_30);
x_146 = l_Lean_addMacroScope(x_30, x_145, x_29);
x_147 = lean_box(0);
lean_inc(x_145);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_147);
lean_ctor_set(x_19, 0, x_145);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_148);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_inc(x_119);
x_149 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_149, 0, x_119);
lean_ctor_set(x_149, 1, x_144);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_11);
lean_inc(x_133);
lean_inc(x_119);
x_150 = l_Lean_Syntax_node2(x_119, x_133, x_23, x_149);
x_151 = l_Array_mkArray0(lean_box(0));
lean_inc(x_133);
lean_inc(x_119);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_119);
lean_ctor_set(x_152, 1, x_133);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_119);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_153);
lean_ctor_set(x_7, 0, x_119);
lean_inc(x_152);
lean_inc(x_119);
x_154 = l_Lean_Syntax_node5(x_119, x_135, x_44, x_141, x_150, x_152, x_7);
lean_inc(x_133);
lean_inc(x_119);
x_155 = l_Lean_Syntax_node1(x_119, x_133, x_154);
x_156 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_119);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_119);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_157);
lean_inc(x_152);
lean_inc(x_130);
lean_inc(x_119);
x_158 = l_Lean_Syntax_node5(x_119, x_130, x_131, x_155, x_152, x_157, x_3);
lean_inc(x_128);
lean_inc(x_119);
x_159 = l_Lean_Syntax_node1(x_119, x_128, x_158);
x_160 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_119);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_119);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_162);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_163 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_162);
lean_inc(x_119);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_119);
lean_ctor_set(x_164, 1, x_162);
lean_inc(x_119);
x_165 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_165, 0, x_119);
lean_ctor_set(x_165, 1, x_31);
lean_ctor_set(x_165, 2, x_32);
lean_ctor_set(x_165, 3, x_33);
x_166 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_121);
x_167 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_166);
x_168 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_169 = l_String_toSubstring_x27(x_168);
x_170 = lean_mk_string_unchecked("Expr", 4, 4);
x_171 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_171);
lean_inc(x_170);
x_172 = l_Lean_Name_mkStr2(x_170, x_171);
x_173 = l_Lean_addMacroScope(x_30, x_172, x_29);
x_174 = l_Lean_Name_mkStr3(x_121, x_170, x_171);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_147);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_33);
lean_inc(x_119);
x_177 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_177, 0, x_119);
lean_ctor_set(x_177, 1, x_169);
lean_ctor_set(x_177, 2, x_173);
lean_ctor_set(x_177, 3, x_176);
lean_inc(x_119);
x_178 = l_Lean_Syntax_node1(x_119, x_133, x_1);
lean_inc(x_119);
x_179 = l_Lean_Syntax_node2(x_119, x_167, x_177, x_178);
lean_inc(x_152);
lean_inc(x_119);
x_180 = l_Lean_Syntax_node5(x_119, x_130, x_165, x_152, x_152, x_157, x_179);
lean_inc(x_119);
x_181 = l_Lean_Syntax_node1(x_119, x_128, x_180);
lean_inc(x_161);
lean_inc(x_119);
x_182 = l_Lean_Syntax_node4(x_119, x_163, x_164, x_181, x_161, x_42);
x_183 = l_Lean_Syntax_node4(x_119, x_125, x_126, x_159, x_161, x_182);
lean_inc(x_9);
x_184 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_183, x_4, x_120);
lean_dec(x_9);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_189 = lean_ctor_get(x_44, 0);
x_190 = lean_ctor_get(x_44, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_44);
x_191 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_189, x_4, x_190);
lean_dec(x_189);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_mk_string_unchecked("Lean", 4, 4);
x_196 = lean_mk_string_unchecked("Parser", 6, 6);
x_197 = lean_mk_string_unchecked("Term", 4, 4);
x_198 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_199 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_198);
lean_inc(x_192);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(2, 2, 0);
} else {
 x_200 = x_194;
 lean_ctor_set_tag(x_200, 2);
}
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_202 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_201);
x_203 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_204 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_203);
lean_inc(x_192);
x_205 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_205, 0, x_192);
lean_ctor_set(x_205, 1, x_36);
lean_ctor_set(x_205, 2, x_38);
lean_ctor_set(x_205, 3, x_33);
x_206 = lean_mk_string_unchecked("null", 4, 4);
x_207 = l_Lean_Name_mkStr1(x_206);
x_208 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_209 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_208);
x_210 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_192);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_192);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_213 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_212);
x_214 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_192);
lean_ctor_set_tag(x_40, 2);
lean_ctor_set(x_40, 1, x_214);
lean_ctor_set(x_40, 0, x_192);
lean_inc(x_192);
x_215 = l_Lean_Syntax_node1(x_192, x_213, x_40);
lean_inc(x_207);
lean_inc(x_192);
x_216 = l_Lean_Syntax_node1(x_192, x_207, x_215);
x_217 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_192);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_217);
lean_ctor_set(x_23, 0, x_192);
x_218 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_218);
x_219 = l_String_toSubstring_x27(x_218);
x_220 = l_Lean_Name_mkStr1(x_218);
lean_inc(x_29);
lean_inc(x_220);
lean_inc(x_30);
x_221 = l_Lean_addMacroScope(x_30, x_220, x_29);
x_222 = lean_box(0);
lean_inc(x_220);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_222);
lean_ctor_set(x_19, 0, x_220);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_223);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_inc(x_192);
x_224 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_224, 0, x_192);
lean_ctor_set(x_224, 1, x_219);
lean_ctor_set(x_224, 2, x_221);
lean_ctor_set(x_224, 3, x_11);
lean_inc(x_207);
lean_inc(x_192);
x_225 = l_Lean_Syntax_node2(x_192, x_207, x_23, x_224);
x_226 = l_Array_mkArray0(lean_box(0));
lean_inc(x_207);
lean_inc(x_192);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_192);
lean_ctor_set(x_227, 1, x_207);
lean_ctor_set(x_227, 2, x_226);
x_228 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_192);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_228);
lean_ctor_set(x_7, 0, x_192);
lean_inc(x_227);
lean_inc(x_192);
x_229 = l_Lean_Syntax_node5(x_192, x_209, x_211, x_216, x_225, x_227, x_7);
lean_inc(x_207);
lean_inc(x_192);
x_230 = l_Lean_Syntax_node1(x_192, x_207, x_229);
x_231 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_192);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_192);
lean_ctor_set(x_232, 1, x_231);
lean_inc(x_232);
lean_inc(x_227);
lean_inc(x_204);
lean_inc(x_192);
x_233 = l_Lean_Syntax_node5(x_192, x_204, x_205, x_230, x_227, x_232, x_3);
lean_inc(x_202);
lean_inc(x_192);
x_234 = l_Lean_Syntax_node1(x_192, x_202, x_233);
x_235 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_192);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_192);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_237);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
x_238 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_237);
lean_inc(x_192);
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_192);
lean_ctor_set(x_239, 1, x_237);
lean_inc(x_192);
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_192);
lean_ctor_set(x_240, 1, x_31);
lean_ctor_set(x_240, 2, x_32);
lean_ctor_set(x_240, 3, x_33);
x_241 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_195);
x_242 = l_Lean_Name_mkStr4(x_195, x_196, x_197, x_241);
x_243 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_244 = l_String_toSubstring_x27(x_243);
x_245 = lean_mk_string_unchecked("Expr", 4, 4);
x_246 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_246);
lean_inc(x_245);
x_247 = l_Lean_Name_mkStr2(x_245, x_246);
x_248 = l_Lean_addMacroScope(x_30, x_247, x_29);
x_249 = l_Lean_Name_mkStr3(x_195, x_245, x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_222);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_33);
lean_inc(x_192);
x_252 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_252, 0, x_192);
lean_ctor_set(x_252, 1, x_244);
lean_ctor_set(x_252, 2, x_248);
lean_ctor_set(x_252, 3, x_251);
lean_inc(x_192);
x_253 = l_Lean_Syntax_node1(x_192, x_207, x_1);
lean_inc(x_192);
x_254 = l_Lean_Syntax_node2(x_192, x_242, x_252, x_253);
lean_inc(x_227);
lean_inc(x_192);
x_255 = l_Lean_Syntax_node5(x_192, x_204, x_240, x_227, x_227, x_232, x_254);
lean_inc(x_192);
x_256 = l_Lean_Syntax_node1(x_192, x_202, x_255);
lean_inc(x_236);
lean_inc(x_192);
x_257 = l_Lean_Syntax_node4(x_192, x_238, x_239, x_256, x_236, x_42);
x_258 = l_Lean_Syntax_node4(x_192, x_199, x_200, x_234, x_236, x_257);
lean_inc(x_9);
x_259 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_258, x_4, x_193);
lean_dec(x_9);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_264 = lean_ctor_get(x_40, 0);
x_265 = lean_ctor_get(x_40, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_40);
x_266 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_267, x_4, x_268);
lean_dec(x_267);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_mk_string_unchecked("Lean", 4, 4);
x_275 = lean_mk_string_unchecked("Parser", 6, 6);
x_276 = lean_mk_string_unchecked("Term", 4, 4);
x_277 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_278 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_277);
lean_inc(x_271);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(2, 2, 0);
} else {
 x_279 = x_273;
 lean_ctor_set_tag(x_279, 2);
}
lean_ctor_set(x_279, 0, x_271);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_281 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_280);
x_282 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_283 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_282);
lean_inc(x_271);
x_284 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_284, 0, x_271);
lean_ctor_set(x_284, 1, x_36);
lean_ctor_set(x_284, 2, x_38);
lean_ctor_set(x_284, 3, x_33);
x_285 = lean_mk_string_unchecked("null", 4, 4);
x_286 = l_Lean_Name_mkStr1(x_285);
x_287 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_288 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_287);
x_289 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_271);
if (lean_is_scalar(x_269)) {
 x_290 = lean_alloc_ctor(2, 2, 0);
} else {
 x_290 = x_269;
 lean_ctor_set_tag(x_290, 2);
}
lean_ctor_set(x_290, 0, x_271);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_292 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_291);
x_293 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_271);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_271);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_271);
x_295 = l_Lean_Syntax_node1(x_271, x_292, x_294);
lean_inc(x_286);
lean_inc(x_271);
x_296 = l_Lean_Syntax_node1(x_271, x_286, x_295);
x_297 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_271);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_297);
lean_ctor_set(x_23, 0, x_271);
x_298 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_298);
x_299 = l_String_toSubstring_x27(x_298);
x_300 = l_Lean_Name_mkStr1(x_298);
lean_inc(x_29);
lean_inc(x_300);
lean_inc(x_30);
x_301 = l_Lean_addMacroScope(x_30, x_300, x_29);
x_302 = lean_box(0);
lean_inc(x_300);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_302);
lean_ctor_set(x_19, 0, x_300);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_303);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_inc(x_271);
x_304 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_304, 0, x_271);
lean_ctor_set(x_304, 1, x_299);
lean_ctor_set(x_304, 2, x_301);
lean_ctor_set(x_304, 3, x_11);
lean_inc(x_286);
lean_inc(x_271);
x_305 = l_Lean_Syntax_node2(x_271, x_286, x_23, x_304);
x_306 = l_Array_mkArray0(lean_box(0));
lean_inc(x_286);
lean_inc(x_271);
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_271);
lean_ctor_set(x_307, 1, x_286);
lean_ctor_set(x_307, 2, x_306);
x_308 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_271);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_308);
lean_ctor_set(x_7, 0, x_271);
lean_inc(x_307);
lean_inc(x_271);
x_309 = l_Lean_Syntax_node5(x_271, x_288, x_290, x_296, x_305, x_307, x_7);
lean_inc(x_286);
lean_inc(x_271);
x_310 = l_Lean_Syntax_node1(x_271, x_286, x_309);
x_311 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_271);
x_312 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_312, 0, x_271);
lean_ctor_set(x_312, 1, x_311);
lean_inc(x_312);
lean_inc(x_307);
lean_inc(x_283);
lean_inc(x_271);
x_313 = l_Lean_Syntax_node5(x_271, x_283, x_284, x_310, x_307, x_312, x_3);
lean_inc(x_281);
lean_inc(x_271);
x_314 = l_Lean_Syntax_node1(x_271, x_281, x_313);
x_315 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_271);
x_316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_316, 0, x_271);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_317);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
x_318 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_317);
lean_inc(x_271);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_271);
lean_ctor_set(x_319, 1, x_317);
lean_inc(x_271);
x_320 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_320, 0, x_271);
lean_ctor_set(x_320, 1, x_31);
lean_ctor_set(x_320, 2, x_32);
lean_ctor_set(x_320, 3, x_33);
x_321 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_274);
x_322 = l_Lean_Name_mkStr4(x_274, x_275, x_276, x_321);
x_323 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_324 = l_String_toSubstring_x27(x_323);
x_325 = lean_mk_string_unchecked("Expr", 4, 4);
x_326 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_326);
lean_inc(x_325);
x_327 = l_Lean_Name_mkStr2(x_325, x_326);
x_328 = l_Lean_addMacroScope(x_30, x_327, x_29);
x_329 = l_Lean_Name_mkStr3(x_274, x_325, x_326);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_302);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_33);
lean_inc(x_271);
x_332 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_332, 0, x_271);
lean_ctor_set(x_332, 1, x_324);
lean_ctor_set(x_332, 2, x_328);
lean_ctor_set(x_332, 3, x_331);
lean_inc(x_271);
x_333 = l_Lean_Syntax_node1(x_271, x_286, x_1);
lean_inc(x_271);
x_334 = l_Lean_Syntax_node2(x_271, x_322, x_332, x_333);
lean_inc(x_307);
lean_inc(x_271);
x_335 = l_Lean_Syntax_node5(x_271, x_283, x_320, x_307, x_307, x_312, x_334);
lean_inc(x_271);
x_336 = l_Lean_Syntax_node1(x_271, x_281, x_335);
lean_inc(x_316);
lean_inc(x_271);
x_337 = l_Lean_Syntax_node4(x_271, x_318, x_319, x_336, x_316, x_264);
x_338 = l_Lean_Syntax_node4(x_271, x_278, x_279, x_314, x_316, x_337);
lean_inc(x_9);
x_339 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_338, x_4, x_272);
lean_dec(x_9);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_342 = x_339;
} else {
 lean_dec_ref(x_339);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_344 = lean_ctor_get(x_23, 0);
x_345 = lean_ctor_get(x_23, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_23);
x_346 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_346);
x_347 = l_Lean_Name_mkStr1(x_346);
x_348 = lean_ctor_get(x_4, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_4, 1);
lean_inc(x_349);
x_350 = l_String_toSubstring_x27(x_346);
lean_inc(x_348);
lean_inc(x_349);
x_351 = l_Lean_addMacroScope(x_349, x_347, x_348);
x_352 = lean_box(0);
lean_inc(x_351);
lean_inc(x_350);
x_353 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_353, 0, x_17);
lean_ctor_set(x_353, 1, x_350);
lean_ctor_set(x_353, 2, x_351);
lean_ctor_set(x_353, 3, x_352);
x_354 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_354);
x_355 = l_String_toSubstring_x27(x_354);
x_356 = l_Lean_Name_mkStr1(x_354);
lean_inc(x_348);
lean_inc(x_349);
x_357 = l_Lean_addMacroScope(x_349, x_356, x_348);
lean_inc(x_357);
lean_inc(x_355);
x_358 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_358, 0, x_344);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set(x_358, 2, x_357);
lean_ctor_set(x_358, 3, x_352);
lean_inc(x_4);
lean_inc(x_9);
x_359 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_358, x_353, x_9, x_4, x_345);
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
x_363 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_361);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_366 = x_363;
} else {
 lean_dec_ref(x_363);
 x_366 = lean_box(0);
}
x_367 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_364, x_4, x_365);
lean_dec(x_364);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
x_371 = lean_mk_string_unchecked("Lean", 4, 4);
x_372 = lean_mk_string_unchecked("Parser", 6, 6);
x_373 = lean_mk_string_unchecked("Term", 4, 4);
x_374 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_375 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_374);
lean_inc(x_368);
if (lean_is_scalar(x_370)) {
 x_376 = lean_alloc_ctor(2, 2, 0);
} else {
 x_376 = x_370;
 lean_ctor_set_tag(x_376, 2);
}
lean_ctor_set(x_376, 0, x_368);
lean_ctor_set(x_376, 1, x_374);
x_377 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_378 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_377);
x_379 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_380 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_379);
lean_inc(x_368);
x_381 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_381, 0, x_368);
lean_ctor_set(x_381, 1, x_355);
lean_ctor_set(x_381, 2, x_357);
lean_ctor_set(x_381, 3, x_352);
x_382 = lean_mk_string_unchecked("null", 4, 4);
x_383 = l_Lean_Name_mkStr1(x_382);
x_384 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_385 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_384);
x_386 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_368);
if (lean_is_scalar(x_366)) {
 x_387 = lean_alloc_ctor(2, 2, 0);
} else {
 x_387 = x_366;
 lean_ctor_set_tag(x_387, 2);
}
lean_ctor_set(x_387, 0, x_368);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_389 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_388);
x_390 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_368);
if (lean_is_scalar(x_362)) {
 x_391 = lean_alloc_ctor(2, 2, 0);
} else {
 x_391 = x_362;
 lean_ctor_set_tag(x_391, 2);
}
lean_ctor_set(x_391, 0, x_368);
lean_ctor_set(x_391, 1, x_390);
lean_inc(x_368);
x_392 = l_Lean_Syntax_node1(x_368, x_389, x_391);
lean_inc(x_383);
lean_inc(x_368);
x_393 = l_Lean_Syntax_node1(x_368, x_383, x_392);
x_394 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_368);
x_395 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_395, 0, x_368);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_396);
x_397 = l_String_toSubstring_x27(x_396);
x_398 = l_Lean_Name_mkStr1(x_396);
lean_inc(x_348);
lean_inc(x_398);
lean_inc(x_349);
x_399 = l_Lean_addMacroScope(x_349, x_398, x_348);
x_400 = lean_box(0);
lean_inc(x_398);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_400);
lean_ctor_set(x_19, 0, x_398);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_352);
lean_ctor_set(x_15, 0, x_401);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_inc(x_368);
x_402 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_402, 0, x_368);
lean_ctor_set(x_402, 1, x_397);
lean_ctor_set(x_402, 2, x_399);
lean_ctor_set(x_402, 3, x_11);
lean_inc(x_383);
lean_inc(x_368);
x_403 = l_Lean_Syntax_node2(x_368, x_383, x_395, x_402);
x_404 = l_Array_mkArray0(lean_box(0));
lean_inc(x_383);
lean_inc(x_368);
x_405 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_405, 0, x_368);
lean_ctor_set(x_405, 1, x_383);
lean_ctor_set(x_405, 2, x_404);
x_406 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_368);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_406);
lean_ctor_set(x_7, 0, x_368);
lean_inc(x_405);
lean_inc(x_368);
x_407 = l_Lean_Syntax_node5(x_368, x_385, x_387, x_393, x_403, x_405, x_7);
lean_inc(x_383);
lean_inc(x_368);
x_408 = l_Lean_Syntax_node1(x_368, x_383, x_407);
x_409 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_368);
x_410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_410, 0, x_368);
lean_ctor_set(x_410, 1, x_409);
lean_inc(x_410);
lean_inc(x_405);
lean_inc(x_380);
lean_inc(x_368);
x_411 = l_Lean_Syntax_node5(x_368, x_380, x_381, x_408, x_405, x_410, x_3);
lean_inc(x_378);
lean_inc(x_368);
x_412 = l_Lean_Syntax_node1(x_368, x_378, x_411);
x_413 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_368);
x_414 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_414, 0, x_368);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_415);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
x_416 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_415);
lean_inc(x_368);
x_417 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_417, 0, x_368);
lean_ctor_set(x_417, 1, x_415);
lean_inc(x_368);
x_418 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_418, 0, x_368);
lean_ctor_set(x_418, 1, x_350);
lean_ctor_set(x_418, 2, x_351);
lean_ctor_set(x_418, 3, x_352);
x_419 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_371);
x_420 = l_Lean_Name_mkStr4(x_371, x_372, x_373, x_419);
x_421 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_422 = l_String_toSubstring_x27(x_421);
x_423 = lean_mk_string_unchecked("Expr", 4, 4);
x_424 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_424);
lean_inc(x_423);
x_425 = l_Lean_Name_mkStr2(x_423, x_424);
x_426 = l_Lean_addMacroScope(x_349, x_425, x_348);
x_427 = l_Lean_Name_mkStr3(x_371, x_423, x_424);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_400);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_352);
lean_inc(x_368);
x_430 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_430, 0, x_368);
lean_ctor_set(x_430, 1, x_422);
lean_ctor_set(x_430, 2, x_426);
lean_ctor_set(x_430, 3, x_429);
lean_inc(x_368);
x_431 = l_Lean_Syntax_node1(x_368, x_383, x_1);
lean_inc(x_368);
x_432 = l_Lean_Syntax_node2(x_368, x_420, x_430, x_431);
lean_inc(x_405);
lean_inc(x_368);
x_433 = l_Lean_Syntax_node5(x_368, x_380, x_418, x_405, x_405, x_410, x_432);
lean_inc(x_368);
x_434 = l_Lean_Syntax_node1(x_368, x_378, x_433);
lean_inc(x_414);
lean_inc(x_368);
x_435 = l_Lean_Syntax_node4(x_368, x_416, x_417, x_434, x_414, x_360);
x_436 = l_Lean_Syntax_node4(x_368, x_375, x_376, x_412, x_414, x_435);
lean_inc(x_9);
x_437 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_436, x_4, x_369);
lean_dec(x_9);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_442 = lean_ctor_get(x_19, 0);
x_443 = lean_ctor_get(x_19, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_19);
x_444 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_442, x_4, x_443);
lean_dec(x_442);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_447 = x_444;
} else {
 lean_dec_ref(x_444);
 x_447 = lean_box(0);
}
x_448 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_448);
x_449 = l_Lean_Name_mkStr1(x_448);
x_450 = lean_ctor_get(x_4, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_4, 1);
lean_inc(x_451);
x_452 = l_String_toSubstring_x27(x_448);
lean_inc(x_450);
lean_inc(x_451);
x_453 = l_Lean_addMacroScope(x_451, x_449, x_450);
x_454 = lean_box(0);
lean_inc(x_453);
lean_inc(x_452);
x_455 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_455, 0, x_17);
lean_ctor_set(x_455, 1, x_452);
lean_ctor_set(x_455, 2, x_453);
lean_ctor_set(x_455, 3, x_454);
x_456 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_456);
x_457 = l_String_toSubstring_x27(x_456);
x_458 = l_Lean_Name_mkStr1(x_456);
lean_inc(x_450);
lean_inc(x_451);
x_459 = l_Lean_addMacroScope(x_451, x_458, x_450);
lean_inc(x_459);
lean_inc(x_457);
x_460 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_460, 0, x_445);
lean_ctor_set(x_460, 1, x_457);
lean_ctor_set(x_460, 2, x_459);
lean_ctor_set(x_460, 3, x_454);
lean_inc(x_4);
lean_inc(x_9);
x_461 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_460, x_455, x_9, x_4, x_446);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_464 = x_461;
} else {
 lean_dec_ref(x_461);
 x_464 = lean_box(0);
}
x_465 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_463);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
x_469 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_466, x_4, x_467);
lean_dec(x_466);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = lean_mk_string_unchecked("Lean", 4, 4);
x_474 = lean_mk_string_unchecked("Parser", 6, 6);
x_475 = lean_mk_string_unchecked("Term", 4, 4);
x_476 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_477 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_476);
lean_inc(x_470);
if (lean_is_scalar(x_472)) {
 x_478 = lean_alloc_ctor(2, 2, 0);
} else {
 x_478 = x_472;
 lean_ctor_set_tag(x_478, 2);
}
lean_ctor_set(x_478, 0, x_470);
lean_ctor_set(x_478, 1, x_476);
x_479 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_480 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_479);
x_481 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_482 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_481);
lean_inc(x_470);
x_483 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_483, 0, x_470);
lean_ctor_set(x_483, 1, x_457);
lean_ctor_set(x_483, 2, x_459);
lean_ctor_set(x_483, 3, x_454);
x_484 = lean_mk_string_unchecked("null", 4, 4);
x_485 = l_Lean_Name_mkStr1(x_484);
x_486 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_487 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_486);
x_488 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_470);
if (lean_is_scalar(x_468)) {
 x_489 = lean_alloc_ctor(2, 2, 0);
} else {
 x_489 = x_468;
 lean_ctor_set_tag(x_489, 2);
}
lean_ctor_set(x_489, 0, x_470);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_491 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_490);
x_492 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_470);
if (lean_is_scalar(x_464)) {
 x_493 = lean_alloc_ctor(2, 2, 0);
} else {
 x_493 = x_464;
 lean_ctor_set_tag(x_493, 2);
}
lean_ctor_set(x_493, 0, x_470);
lean_ctor_set(x_493, 1, x_492);
lean_inc(x_470);
x_494 = l_Lean_Syntax_node1(x_470, x_491, x_493);
lean_inc(x_485);
lean_inc(x_470);
x_495 = l_Lean_Syntax_node1(x_470, x_485, x_494);
x_496 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_470);
if (lean_is_scalar(x_447)) {
 x_497 = lean_alloc_ctor(2, 2, 0);
} else {
 x_497 = x_447;
 lean_ctor_set_tag(x_497, 2);
}
lean_ctor_set(x_497, 0, x_470);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_498);
x_499 = l_String_toSubstring_x27(x_498);
x_500 = l_Lean_Name_mkStr1(x_498);
lean_inc(x_450);
lean_inc(x_500);
lean_inc(x_451);
x_501 = l_Lean_addMacroScope(x_451, x_500, x_450);
x_502 = lean_box(0);
lean_inc(x_500);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_504, 0, x_500);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_454);
lean_ctor_set(x_15, 0, x_504);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_503);
lean_inc(x_470);
x_505 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_505, 0, x_470);
lean_ctor_set(x_505, 1, x_499);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_11);
lean_inc(x_485);
lean_inc(x_470);
x_506 = l_Lean_Syntax_node2(x_470, x_485, x_497, x_505);
x_507 = l_Array_mkArray0(lean_box(0));
lean_inc(x_485);
lean_inc(x_470);
x_508 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_508, 0, x_470);
lean_ctor_set(x_508, 1, x_485);
lean_ctor_set(x_508, 2, x_507);
x_509 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_470);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_509);
lean_ctor_set(x_7, 0, x_470);
lean_inc(x_508);
lean_inc(x_470);
x_510 = l_Lean_Syntax_node5(x_470, x_487, x_489, x_495, x_506, x_508, x_7);
lean_inc(x_485);
lean_inc(x_470);
x_511 = l_Lean_Syntax_node1(x_470, x_485, x_510);
x_512 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_470);
x_513 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_513, 0, x_470);
lean_ctor_set(x_513, 1, x_512);
lean_inc(x_513);
lean_inc(x_508);
lean_inc(x_482);
lean_inc(x_470);
x_514 = l_Lean_Syntax_node5(x_470, x_482, x_483, x_511, x_508, x_513, x_3);
lean_inc(x_480);
lean_inc(x_470);
x_515 = l_Lean_Syntax_node1(x_470, x_480, x_514);
x_516 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_470);
x_517 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_517, 0, x_470);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_518);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
x_519 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_518);
lean_inc(x_470);
x_520 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_520, 0, x_470);
lean_ctor_set(x_520, 1, x_518);
lean_inc(x_470);
x_521 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_521, 0, x_470);
lean_ctor_set(x_521, 1, x_452);
lean_ctor_set(x_521, 2, x_453);
lean_ctor_set(x_521, 3, x_454);
x_522 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_473);
x_523 = l_Lean_Name_mkStr4(x_473, x_474, x_475, x_522);
x_524 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_525 = l_String_toSubstring_x27(x_524);
x_526 = lean_mk_string_unchecked("Expr", 4, 4);
x_527 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_527);
lean_inc(x_526);
x_528 = l_Lean_Name_mkStr2(x_526, x_527);
x_529 = l_Lean_addMacroScope(x_451, x_528, x_450);
x_530 = l_Lean_Name_mkStr3(x_473, x_526, x_527);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_502);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_454);
lean_inc(x_470);
x_533 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_533, 0, x_470);
lean_ctor_set(x_533, 1, x_525);
lean_ctor_set(x_533, 2, x_529);
lean_ctor_set(x_533, 3, x_532);
lean_inc(x_470);
x_534 = l_Lean_Syntax_node1(x_470, x_485, x_1);
lean_inc(x_470);
x_535 = l_Lean_Syntax_node2(x_470, x_523, x_533, x_534);
lean_inc(x_508);
lean_inc(x_470);
x_536 = l_Lean_Syntax_node5(x_470, x_482, x_521, x_508, x_508, x_513, x_535);
lean_inc(x_470);
x_537 = l_Lean_Syntax_node1(x_470, x_480, x_536);
lean_inc(x_517);
lean_inc(x_470);
x_538 = l_Lean_Syntax_node4(x_470, x_519, x_520, x_537, x_517, x_462);
x_539 = l_Lean_Syntax_node4(x_470, x_477, x_478, x_515, x_517, x_538);
lean_inc(x_9);
x_540 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_539, x_4, x_471);
lean_dec(x_9);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_545 = lean_ctor_get(x_15, 0);
x_546 = lean_ctor_get(x_15, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_15);
x_547 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_546);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_550 = x_547;
} else {
 lean_dec_ref(x_547);
 x_550 = lean_box(0);
}
x_551 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_548, x_4, x_549);
lean_dec(x_548);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_554 = x_551;
} else {
 lean_dec_ref(x_551);
 x_554 = lean_box(0);
}
x_555 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_555);
x_556 = l_Lean_Name_mkStr1(x_555);
x_557 = lean_ctor_get(x_4, 2);
lean_inc(x_557);
x_558 = lean_ctor_get(x_4, 1);
lean_inc(x_558);
x_559 = l_String_toSubstring_x27(x_555);
lean_inc(x_557);
lean_inc(x_558);
x_560 = l_Lean_addMacroScope(x_558, x_556, x_557);
x_561 = lean_box(0);
lean_inc(x_560);
lean_inc(x_559);
x_562 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_562, 0, x_545);
lean_ctor_set(x_562, 1, x_559);
lean_ctor_set(x_562, 2, x_560);
lean_ctor_set(x_562, 3, x_561);
x_563 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_563);
x_564 = l_String_toSubstring_x27(x_563);
x_565 = l_Lean_Name_mkStr1(x_563);
lean_inc(x_557);
lean_inc(x_558);
x_566 = l_Lean_addMacroScope(x_558, x_565, x_557);
lean_inc(x_566);
lean_inc(x_564);
x_567 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_567, 0, x_552);
lean_ctor_set(x_567, 1, x_564);
lean_ctor_set(x_567, 2, x_566);
lean_ctor_set(x_567, 3, x_561);
lean_inc(x_4);
lean_inc(x_9);
x_568 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_567, x_562, x_9, x_4, x_553);
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_571 = x_568;
} else {
 lean_dec_ref(x_568);
 x_571 = lean_box(0);
}
x_572 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_570);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_575 = x_572;
} else {
 lean_dec_ref(x_572);
 x_575 = lean_box(0);
}
x_576 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_573, x_4, x_574);
lean_dec(x_573);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
x_580 = lean_mk_string_unchecked("Lean", 4, 4);
x_581 = lean_mk_string_unchecked("Parser", 6, 6);
x_582 = lean_mk_string_unchecked("Term", 4, 4);
x_583 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_583);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_584 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_583);
lean_inc(x_577);
if (lean_is_scalar(x_579)) {
 x_585 = lean_alloc_ctor(2, 2, 0);
} else {
 x_585 = x_579;
 lean_ctor_set_tag(x_585, 2);
}
lean_ctor_set(x_585, 0, x_577);
lean_ctor_set(x_585, 1, x_583);
x_586 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_587 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_586);
x_588 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_589 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_588);
lean_inc(x_577);
x_590 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_590, 0, x_577);
lean_ctor_set(x_590, 1, x_564);
lean_ctor_set(x_590, 2, x_566);
lean_ctor_set(x_590, 3, x_561);
x_591 = lean_mk_string_unchecked("null", 4, 4);
x_592 = l_Lean_Name_mkStr1(x_591);
x_593 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_594 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_593);
x_595 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_577);
if (lean_is_scalar(x_575)) {
 x_596 = lean_alloc_ctor(2, 2, 0);
} else {
 x_596 = x_575;
 lean_ctor_set_tag(x_596, 2);
}
lean_ctor_set(x_596, 0, x_577);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_598 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_597);
x_599 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_577);
if (lean_is_scalar(x_571)) {
 x_600 = lean_alloc_ctor(2, 2, 0);
} else {
 x_600 = x_571;
 lean_ctor_set_tag(x_600, 2);
}
lean_ctor_set(x_600, 0, x_577);
lean_ctor_set(x_600, 1, x_599);
lean_inc(x_577);
x_601 = l_Lean_Syntax_node1(x_577, x_598, x_600);
lean_inc(x_592);
lean_inc(x_577);
x_602 = l_Lean_Syntax_node1(x_577, x_592, x_601);
x_603 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_577);
if (lean_is_scalar(x_554)) {
 x_604 = lean_alloc_ctor(2, 2, 0);
} else {
 x_604 = x_554;
 lean_ctor_set_tag(x_604, 2);
}
lean_ctor_set(x_604, 0, x_577);
lean_ctor_set(x_604, 1, x_603);
x_605 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_605);
x_606 = l_String_toSubstring_x27(x_605);
x_607 = l_Lean_Name_mkStr1(x_605);
lean_inc(x_557);
lean_inc(x_607);
lean_inc(x_558);
x_608 = l_Lean_addMacroScope(x_558, x_607, x_557);
x_609 = lean_box(0);
lean_inc(x_607);
if (lean_is_scalar(x_550)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_550;
 lean_ctor_set_tag(x_610, 1);
}
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_611, 0, x_607);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_561);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_612);
lean_ctor_set(x_11, 0, x_610);
lean_inc(x_577);
x_613 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_613, 0, x_577);
lean_ctor_set(x_613, 1, x_606);
lean_ctor_set(x_613, 2, x_608);
lean_ctor_set(x_613, 3, x_11);
lean_inc(x_592);
lean_inc(x_577);
x_614 = l_Lean_Syntax_node2(x_577, x_592, x_604, x_613);
x_615 = l_Array_mkArray0(lean_box(0));
lean_inc(x_592);
lean_inc(x_577);
x_616 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_616, 0, x_577);
lean_ctor_set(x_616, 1, x_592);
lean_ctor_set(x_616, 2, x_615);
x_617 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_577);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_617);
lean_ctor_set(x_7, 0, x_577);
lean_inc(x_616);
lean_inc(x_577);
x_618 = l_Lean_Syntax_node5(x_577, x_594, x_596, x_602, x_614, x_616, x_7);
lean_inc(x_592);
lean_inc(x_577);
x_619 = l_Lean_Syntax_node1(x_577, x_592, x_618);
x_620 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_577);
x_621 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_621, 0, x_577);
lean_ctor_set(x_621, 1, x_620);
lean_inc(x_621);
lean_inc(x_616);
lean_inc(x_589);
lean_inc(x_577);
x_622 = l_Lean_Syntax_node5(x_577, x_589, x_590, x_619, x_616, x_621, x_3);
lean_inc(x_587);
lean_inc(x_577);
x_623 = l_Lean_Syntax_node1(x_577, x_587, x_622);
x_624 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_577);
x_625 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_625, 0, x_577);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_626);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
x_627 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_626);
lean_inc(x_577);
x_628 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_628, 0, x_577);
lean_ctor_set(x_628, 1, x_626);
lean_inc(x_577);
x_629 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_629, 0, x_577);
lean_ctor_set(x_629, 1, x_559);
lean_ctor_set(x_629, 2, x_560);
lean_ctor_set(x_629, 3, x_561);
x_630 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_580);
x_631 = l_Lean_Name_mkStr4(x_580, x_581, x_582, x_630);
x_632 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_633 = l_String_toSubstring_x27(x_632);
x_634 = lean_mk_string_unchecked("Expr", 4, 4);
x_635 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_635);
lean_inc(x_634);
x_636 = l_Lean_Name_mkStr2(x_634, x_635);
x_637 = l_Lean_addMacroScope(x_558, x_636, x_557);
x_638 = l_Lean_Name_mkStr3(x_580, x_634, x_635);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_609);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_561);
lean_inc(x_577);
x_641 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_641, 0, x_577);
lean_ctor_set(x_641, 1, x_633);
lean_ctor_set(x_641, 2, x_637);
lean_ctor_set(x_641, 3, x_640);
lean_inc(x_577);
x_642 = l_Lean_Syntax_node1(x_577, x_592, x_1);
lean_inc(x_577);
x_643 = l_Lean_Syntax_node2(x_577, x_631, x_641, x_642);
lean_inc(x_616);
lean_inc(x_577);
x_644 = l_Lean_Syntax_node5(x_577, x_589, x_629, x_616, x_616, x_621, x_643);
lean_inc(x_577);
x_645 = l_Lean_Syntax_node1(x_577, x_587, x_644);
lean_inc(x_625);
lean_inc(x_577);
x_646 = l_Lean_Syntax_node4(x_577, x_627, x_628, x_645, x_625, x_569);
x_647 = l_Lean_Syntax_node4(x_577, x_584, x_585, x_623, x_625, x_646);
lean_inc(x_9);
x_648 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_647, x_4, x_578);
lean_dec(x_9);
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_651 = x_648;
} else {
 lean_dec_ref(x_648);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_653 = lean_ctor_get(x_11, 0);
x_654 = lean_ctor_get(x_11, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_11);
x_655 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_653, x_4, x_654);
lean_dec(x_653);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_658 = x_655;
} else {
 lean_dec_ref(x_655);
 x_658 = lean_box(0);
}
x_659 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_657);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_662 = x_659;
} else {
 lean_dec_ref(x_659);
 x_662 = lean_box(0);
}
x_663 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_660, x_4, x_661);
lean_dec(x_660);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
x_667 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_667);
x_668 = l_Lean_Name_mkStr1(x_667);
x_669 = lean_ctor_get(x_4, 2);
lean_inc(x_669);
x_670 = lean_ctor_get(x_4, 1);
lean_inc(x_670);
x_671 = l_String_toSubstring_x27(x_667);
lean_inc(x_669);
lean_inc(x_670);
x_672 = l_Lean_addMacroScope(x_670, x_668, x_669);
x_673 = lean_box(0);
lean_inc(x_672);
lean_inc(x_671);
x_674 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_674, 0, x_656);
lean_ctor_set(x_674, 1, x_671);
lean_ctor_set(x_674, 2, x_672);
lean_ctor_set(x_674, 3, x_673);
x_675 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_675);
x_676 = l_String_toSubstring_x27(x_675);
x_677 = l_Lean_Name_mkStr1(x_675);
lean_inc(x_669);
lean_inc(x_670);
x_678 = l_Lean_addMacroScope(x_670, x_677, x_669);
lean_inc(x_678);
lean_inc(x_676);
x_679 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_679, 0, x_664);
lean_ctor_set(x_679, 1, x_676);
lean_ctor_set(x_679, 2, x_678);
lean_ctor_set(x_679, 3, x_673);
lean_inc(x_4);
lean_inc(x_9);
x_680 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_679, x_674, x_9, x_4, x_665);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
x_684 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_682);
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_687 = x_684;
} else {
 lean_dec_ref(x_684);
 x_687 = lean_box(0);
}
x_688 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_685, x_4, x_686);
lean_dec(x_685);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_691 = x_688;
} else {
 lean_dec_ref(x_688);
 x_691 = lean_box(0);
}
x_692 = lean_mk_string_unchecked("Lean", 4, 4);
x_693 = lean_mk_string_unchecked("Parser", 6, 6);
x_694 = lean_mk_string_unchecked("Term", 4, 4);
x_695 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_695);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_696 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_695);
lean_inc(x_689);
if (lean_is_scalar(x_691)) {
 x_697 = lean_alloc_ctor(2, 2, 0);
} else {
 x_697 = x_691;
 lean_ctor_set_tag(x_697, 2);
}
lean_ctor_set(x_697, 0, x_689);
lean_ctor_set(x_697, 1, x_695);
x_698 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_699 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_698);
x_700 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_701 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_700);
lean_inc(x_689);
x_702 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_702, 0, x_689);
lean_ctor_set(x_702, 1, x_676);
lean_ctor_set(x_702, 2, x_678);
lean_ctor_set(x_702, 3, x_673);
x_703 = lean_mk_string_unchecked("null", 4, 4);
x_704 = l_Lean_Name_mkStr1(x_703);
x_705 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_706 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_705);
x_707 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_689);
if (lean_is_scalar(x_687)) {
 x_708 = lean_alloc_ctor(2, 2, 0);
} else {
 x_708 = x_687;
 lean_ctor_set_tag(x_708, 2);
}
lean_ctor_set(x_708, 0, x_689);
lean_ctor_set(x_708, 1, x_707);
x_709 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_710 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_709);
x_711 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_689);
if (lean_is_scalar(x_683)) {
 x_712 = lean_alloc_ctor(2, 2, 0);
} else {
 x_712 = x_683;
 lean_ctor_set_tag(x_712, 2);
}
lean_ctor_set(x_712, 0, x_689);
lean_ctor_set(x_712, 1, x_711);
lean_inc(x_689);
x_713 = l_Lean_Syntax_node1(x_689, x_710, x_712);
lean_inc(x_704);
lean_inc(x_689);
x_714 = l_Lean_Syntax_node1(x_689, x_704, x_713);
x_715 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_689);
if (lean_is_scalar(x_666)) {
 x_716 = lean_alloc_ctor(2, 2, 0);
} else {
 x_716 = x_666;
 lean_ctor_set_tag(x_716, 2);
}
lean_ctor_set(x_716, 0, x_689);
lean_ctor_set(x_716, 1, x_715);
x_717 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_717);
x_718 = l_String_toSubstring_x27(x_717);
x_719 = l_Lean_Name_mkStr1(x_717);
lean_inc(x_669);
lean_inc(x_719);
lean_inc(x_670);
x_720 = l_Lean_addMacroScope(x_670, x_719, x_669);
x_721 = lean_box(0);
lean_inc(x_719);
if (lean_is_scalar(x_662)) {
 x_722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_722 = x_662;
 lean_ctor_set_tag(x_722, 1);
}
lean_ctor_set(x_722, 0, x_719);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_723, 0, x_719);
if (lean_is_scalar(x_658)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_658;
 lean_ctor_set_tag(x_724, 1);
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_673);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_722);
lean_ctor_set(x_725, 1, x_724);
lean_inc(x_689);
x_726 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_726, 0, x_689);
lean_ctor_set(x_726, 1, x_718);
lean_ctor_set(x_726, 2, x_720);
lean_ctor_set(x_726, 3, x_725);
lean_inc(x_704);
lean_inc(x_689);
x_727 = l_Lean_Syntax_node2(x_689, x_704, x_716, x_726);
x_728 = l_Array_mkArray0(lean_box(0));
lean_inc(x_704);
lean_inc(x_689);
x_729 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_729, 0, x_689);
lean_ctor_set(x_729, 1, x_704);
lean_ctor_set(x_729, 2, x_728);
x_730 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_689);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_730);
lean_ctor_set(x_7, 0, x_689);
lean_inc(x_729);
lean_inc(x_689);
x_731 = l_Lean_Syntax_node5(x_689, x_706, x_708, x_714, x_727, x_729, x_7);
lean_inc(x_704);
lean_inc(x_689);
x_732 = l_Lean_Syntax_node1(x_689, x_704, x_731);
x_733 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_689);
x_734 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_734, 0, x_689);
lean_ctor_set(x_734, 1, x_733);
lean_inc(x_734);
lean_inc(x_729);
lean_inc(x_701);
lean_inc(x_689);
x_735 = l_Lean_Syntax_node5(x_689, x_701, x_702, x_732, x_729, x_734, x_3);
lean_inc(x_699);
lean_inc(x_689);
x_736 = l_Lean_Syntax_node1(x_689, x_699, x_735);
x_737 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_689);
x_738 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_738, 0, x_689);
lean_ctor_set(x_738, 1, x_737);
x_739 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_739);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
x_740 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_739);
lean_inc(x_689);
x_741 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_741, 0, x_689);
lean_ctor_set(x_741, 1, x_739);
lean_inc(x_689);
x_742 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_742, 0, x_689);
lean_ctor_set(x_742, 1, x_671);
lean_ctor_set(x_742, 2, x_672);
lean_ctor_set(x_742, 3, x_673);
x_743 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_692);
x_744 = l_Lean_Name_mkStr4(x_692, x_693, x_694, x_743);
x_745 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_746 = l_String_toSubstring_x27(x_745);
x_747 = lean_mk_string_unchecked("Expr", 4, 4);
x_748 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_748);
lean_inc(x_747);
x_749 = l_Lean_Name_mkStr2(x_747, x_748);
x_750 = l_Lean_addMacroScope(x_670, x_749, x_669);
x_751 = l_Lean_Name_mkStr3(x_692, x_747, x_748);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_721);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_673);
lean_inc(x_689);
x_754 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_754, 0, x_689);
lean_ctor_set(x_754, 1, x_746);
lean_ctor_set(x_754, 2, x_750);
lean_ctor_set(x_754, 3, x_753);
lean_inc(x_689);
x_755 = l_Lean_Syntax_node1(x_689, x_704, x_1);
lean_inc(x_689);
x_756 = l_Lean_Syntax_node2(x_689, x_744, x_754, x_755);
lean_inc(x_729);
lean_inc(x_689);
x_757 = l_Lean_Syntax_node5(x_689, x_701, x_742, x_729, x_729, x_734, x_756);
lean_inc(x_689);
x_758 = l_Lean_Syntax_node1(x_689, x_699, x_757);
lean_inc(x_738);
lean_inc(x_689);
x_759 = l_Lean_Syntax_node4(x_689, x_740, x_741, x_758, x_738, x_681);
x_760 = l_Lean_Syntax_node4(x_689, x_696, x_697, x_736, x_738, x_759);
lean_inc(x_9);
x_761 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_9, x_9, x_760, x_4, x_690);
lean_dec(x_9);
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_764 = x_761;
} else {
 lean_dec_ref(x_761);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(0, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_766 = lean_ctor_get(x_7, 0);
x_767 = lean_ctor_get(x_7, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_7);
x_768 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_767);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 x_771 = x_768;
} else {
 lean_dec_ref(x_768);
 x_771 = lean_box(0);
}
x_772 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_769, x_4, x_770);
lean_dec(x_769);
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_775 = x_772;
} else {
 lean_dec_ref(x_772);
 x_775 = lean_box(0);
}
x_776 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_774);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_779 = x_776;
} else {
 lean_dec_ref(x_776);
 x_779 = lean_box(0);
}
x_780 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_777, x_4, x_778);
lean_dec(x_777);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_783 = x_780;
} else {
 lean_dec_ref(x_780);
 x_783 = lean_box(0);
}
x_784 = lean_mk_string_unchecked("__discr", 7, 7);
lean_inc(x_784);
x_785 = l_Lean_Name_mkStr1(x_784);
x_786 = lean_ctor_get(x_4, 2);
lean_inc(x_786);
x_787 = lean_ctor_get(x_4, 1);
lean_inc(x_787);
x_788 = l_String_toSubstring_x27(x_784);
lean_inc(x_786);
lean_inc(x_787);
x_789 = l_Lean_addMacroScope(x_787, x_785, x_786);
x_790 = lean_box(0);
lean_inc(x_789);
lean_inc(x_788);
x_791 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_791, 0, x_773);
lean_ctor_set(x_791, 1, x_788);
lean_ctor_set(x_791, 2, x_789);
lean_ctor_set(x_791, 3, x_790);
x_792 = lean_mk_string_unchecked("__do_jp", 7, 7);
lean_inc(x_792);
x_793 = l_String_toSubstring_x27(x_792);
x_794 = l_Lean_Name_mkStr1(x_792);
lean_inc(x_786);
lean_inc(x_787);
x_795 = l_Lean_addMacroScope(x_787, x_794, x_786);
lean_inc(x_795);
lean_inc(x_793);
x_796 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_796, 0, x_781);
lean_ctor_set(x_796, 1, x_793);
lean_ctor_set(x_796, 2, x_795);
lean_ctor_set(x_796, 3, x_790);
lean_inc(x_4);
lean_inc(x_766);
x_797 = l_Lean_Elab_Term_MatchExpr_generate_loop(x_796, x_791, x_766, x_4, x_782);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_800 = x_797;
} else {
 lean_dec_ref(x_797);
 x_800 = lean_box(0);
}
x_801 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_4, x_4, x_799);
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_804 = x_801;
} else {
 lean_dec_ref(x_801);
 x_804 = lean_box(0);
}
x_805 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_802, x_4, x_803);
lean_dec(x_802);
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_808 = x_805;
} else {
 lean_dec_ref(x_805);
 x_808 = lean_box(0);
}
x_809 = lean_mk_string_unchecked("Lean", 4, 4);
x_810 = lean_mk_string_unchecked("Parser", 6, 6);
x_811 = lean_mk_string_unchecked("Term", 4, 4);
x_812 = lean_mk_string_unchecked("let_delayed", 11, 11);
lean_inc(x_812);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_813 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_812);
lean_inc(x_806);
if (lean_is_scalar(x_808)) {
 x_814 = lean_alloc_ctor(2, 2, 0);
} else {
 x_814 = x_808;
 lean_ctor_set_tag(x_814, 2);
}
lean_ctor_set(x_814, 0, x_806);
lean_ctor_set(x_814, 1, x_812);
x_815 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_816 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_815);
x_817 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_818 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_817);
lean_inc(x_806);
x_819 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_819, 0, x_806);
lean_ctor_set(x_819, 1, x_793);
lean_ctor_set(x_819, 2, x_795);
lean_ctor_set(x_819, 3, x_790);
x_820 = lean_mk_string_unchecked("null", 4, 4);
x_821 = l_Lean_Name_mkStr1(x_820);
x_822 = lean_mk_string_unchecked("explicitBinder", 14, 14);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_823 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_822);
x_824 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_806);
if (lean_is_scalar(x_804)) {
 x_825 = lean_alloc_ctor(2, 2, 0);
} else {
 x_825 = x_804;
 lean_ctor_set_tag(x_825, 2);
}
lean_ctor_set(x_825, 0, x_806);
lean_ctor_set(x_825, 1, x_824);
x_826 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_827 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_826);
x_828 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_806);
if (lean_is_scalar(x_800)) {
 x_829 = lean_alloc_ctor(2, 2, 0);
} else {
 x_829 = x_800;
 lean_ctor_set_tag(x_829, 2);
}
lean_ctor_set(x_829, 0, x_806);
lean_ctor_set(x_829, 1, x_828);
lean_inc(x_806);
x_830 = l_Lean_Syntax_node1(x_806, x_827, x_829);
lean_inc(x_821);
lean_inc(x_806);
x_831 = l_Lean_Syntax_node1(x_806, x_821, x_830);
x_832 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_806);
if (lean_is_scalar(x_783)) {
 x_833 = lean_alloc_ctor(2, 2, 0);
} else {
 x_833 = x_783;
 lean_ctor_set_tag(x_833, 2);
}
lean_ctor_set(x_833, 0, x_806);
lean_ctor_set(x_833, 1, x_832);
x_834 = lean_mk_string_unchecked("Unit", 4, 4);
lean_inc(x_834);
x_835 = l_String_toSubstring_x27(x_834);
x_836 = l_Lean_Name_mkStr1(x_834);
lean_inc(x_786);
lean_inc(x_836);
lean_inc(x_787);
x_837 = l_Lean_addMacroScope(x_787, x_836, x_786);
x_838 = lean_box(0);
lean_inc(x_836);
if (lean_is_scalar(x_779)) {
 x_839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_839 = x_779;
 lean_ctor_set_tag(x_839, 1);
}
lean_ctor_set(x_839, 0, x_836);
lean_ctor_set(x_839, 1, x_838);
x_840 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_840, 0, x_836);
if (lean_is_scalar(x_775)) {
 x_841 = lean_alloc_ctor(1, 2, 0);
} else {
 x_841 = x_775;
 lean_ctor_set_tag(x_841, 1);
}
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_790);
if (lean_is_scalar(x_771)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_771;
 lean_ctor_set_tag(x_842, 1);
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_841);
lean_inc(x_806);
x_843 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_843, 0, x_806);
lean_ctor_set(x_843, 1, x_835);
lean_ctor_set(x_843, 2, x_837);
lean_ctor_set(x_843, 3, x_842);
lean_inc(x_821);
lean_inc(x_806);
x_844 = l_Lean_Syntax_node2(x_806, x_821, x_833, x_843);
x_845 = l_Array_mkArray0(lean_box(0));
lean_inc(x_821);
lean_inc(x_806);
x_846 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_846, 0, x_806);
lean_ctor_set(x_846, 1, x_821);
lean_ctor_set(x_846, 2, x_845);
x_847 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_806);
x_848 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_848, 0, x_806);
lean_ctor_set(x_848, 1, x_847);
lean_inc(x_846);
lean_inc(x_806);
x_849 = l_Lean_Syntax_node5(x_806, x_823, x_825, x_831, x_844, x_846, x_848);
lean_inc(x_821);
lean_inc(x_806);
x_850 = l_Lean_Syntax_node1(x_806, x_821, x_849);
x_851 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_806);
x_852 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_852, 0, x_806);
lean_ctor_set(x_852, 1, x_851);
lean_inc(x_852);
lean_inc(x_846);
lean_inc(x_818);
lean_inc(x_806);
x_853 = l_Lean_Syntax_node5(x_806, x_818, x_819, x_850, x_846, x_852, x_3);
lean_inc(x_816);
lean_inc(x_806);
x_854 = l_Lean_Syntax_node1(x_806, x_816, x_853);
x_855 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_806);
x_856 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_856, 0, x_806);
lean_ctor_set(x_856, 1, x_855);
x_857 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_857);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_858 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_857);
lean_inc(x_806);
x_859 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_859, 0, x_806);
lean_ctor_set(x_859, 1, x_857);
lean_inc(x_806);
x_860 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_860, 0, x_806);
lean_ctor_set(x_860, 1, x_788);
lean_ctor_set(x_860, 2, x_789);
lean_ctor_set(x_860, 3, x_790);
x_861 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_809);
x_862 = l_Lean_Name_mkStr4(x_809, x_810, x_811, x_861);
x_863 = lean_mk_string_unchecked("Expr.cleanupAnnotations", 23, 23);
x_864 = l_String_toSubstring_x27(x_863);
x_865 = lean_mk_string_unchecked("Expr", 4, 4);
x_866 = lean_mk_string_unchecked("cleanupAnnotations", 18, 18);
lean_inc(x_866);
lean_inc(x_865);
x_867 = l_Lean_Name_mkStr2(x_865, x_866);
x_868 = l_Lean_addMacroScope(x_787, x_867, x_786);
x_869 = l_Lean_Name_mkStr3(x_809, x_865, x_866);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_838);
x_871 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_790);
lean_inc(x_806);
x_872 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_872, 0, x_806);
lean_ctor_set(x_872, 1, x_864);
lean_ctor_set(x_872, 2, x_868);
lean_ctor_set(x_872, 3, x_871);
lean_inc(x_806);
x_873 = l_Lean_Syntax_node1(x_806, x_821, x_1);
lean_inc(x_806);
x_874 = l_Lean_Syntax_node2(x_806, x_862, x_872, x_873);
lean_inc(x_846);
lean_inc(x_806);
x_875 = l_Lean_Syntax_node5(x_806, x_818, x_860, x_846, x_846, x_852, x_874);
lean_inc(x_806);
x_876 = l_Lean_Syntax_node1(x_806, x_816, x_875);
lean_inc(x_856);
lean_inc(x_806);
x_877 = l_Lean_Syntax_node4(x_806, x_858, x_859, x_876, x_856, x_798);
x_878 = l_Lean_Syntax_node4(x_806, x_813, x_814, x_854, x_856, x_877);
lean_inc(x_766);
x_879 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_766, x_766, x_878, x_4, x_807);
lean_dec(x_766);
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 x_882 = x_879;
} else {
 lean_dec_ref(x_879);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_Elab_Term_MatchExpr_generate_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_MatchExpr_generate___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_generate___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_MatchExpr_generate___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_9 = x_1;
} else {
 lean_dec_ref(x_1);
 x_9 = lean_box(0);
}
lean_inc(x_7);
x_15 = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_16 = lean_mk_string_unchecked("unexpected `match_expr` alternative", 35, 35);
x_17 = l_Lean_Macro_throwErrorAt(lean_box(0), x_7, x_16, x_3, x_4);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_7);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_10 = x_22;
x_11 = x_4;
goto block_14;
}
block_14:
{
lean_object* x_12; 
if (lean_is_scalar(x_9)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_9;
}
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_8;
x_2 = x_12;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchExpr_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_to_list(x_2);
x_7 = lean_box(0);
x_8 = l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0(x_6, x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("unexpected `match_expr` else-alternative", 40, 40);
x_13 = l_Lean_Macro_throwErrorAt(lean_box(0), x_3, x_12, x_4, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Elab_Term_MatchExpr_generate(x_1, x_9, x_14, x_4, x_10);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___Lean_Elab_Term_MatchExpr_main_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("matchExpr", 9, 9);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArg(x_14, x_11);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = l_Lean_Syntax_getArg(x_14, x_12);
lean_dec(x_14);
x_19 = l_Lean_Elab_Term_MatchExpr_main(x_15, x_17, x_18, x_2, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("matchExpr", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandMatchExpr", 15, 15);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchExpr), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandMatchExpr", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(203u);
x_8 = lean_unsigned_to_nat(44u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(207u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(48u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(63u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("letExpr", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_mk_string_unchecked("matchExprPat", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(5u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(7u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 5);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_SourceInfo_fromRef(x_23, x_25);
x_27 = lean_mk_string_unchecked("matchExpr", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_mk_string_unchecked("match_expr", 10, 10);
lean_inc(x_26);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_26);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("matchExprAlts", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_mk_string_unchecked("matchExprAlt", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_37);
x_39 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_26);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_26);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_26);
x_43 = l_Lean_Syntax_node4(x_26, x_38, x_40, x_12, x_42, x_22);
lean_inc(x_26);
x_44 = l_Lean_Syntax_node1(x_26, x_36, x_43);
x_45 = lean_mk_string_unchecked("matchExprElseAlt", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_46 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_45);
x_47 = lean_mk_string_unchecked("hole", 4, 4);
x_48 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_47);
x_49 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_26);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_26);
x_51 = l_Lean_Syntax_node1(x_26, x_48, x_50);
lean_inc(x_26);
x_52 = l_Lean_Syntax_node4(x_26, x_46, x_40, x_51, x_42, x_20);
lean_inc(x_26);
x_53 = l_Lean_Syntax_node2(x_26, x_34, x_44, x_52);
x_54 = l_Lean_Syntax_node4(x_26, x_28, x_30, x_18, x_32, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandLetExpr(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandLetExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("letExpr", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandLetExpr", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetExpr___boxed), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("expandLetExpr", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(209u);
x_8 = lean_unsigned_to_nat(42u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(215u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(46u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(59u);
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
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MatchExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandMatchExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandLetExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
