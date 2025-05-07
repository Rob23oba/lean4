// Lean compiler output
// Module: Lean.Elab.Notation
// Imports: Lean.Elab.Syntax Lean.Elab.AuxDef Lean.Elab.BuiltinNotation
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
lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotation(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(size_t, size_t, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNotation_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getId(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_mk_string_unchecked("ident", 5, 5);
x_4 = l_Lean_Name_mkStr1(x_3);
lean_inc(x_2);
x_5 = l_Lean_Syntax_isOfKind(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_8, x_10, x_7);
lean_ctor_set(x_2, 2, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_15, x_17, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
else
{
return x_2;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_1);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
if (x_22 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_20);
x_24 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_25 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_2, x_1, x_23, x_24);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_mk_string_unchecked("term", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Syntax_mkAntiquotNode(x_27, x_2, x_20, x_28, x_5);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_mk_string_unchecked("app", 3, 3);
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; uint8_t x_83; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_11 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_14 = l_Lean_Name_mkStr1(x_11);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_box(0);
lean_inc(x_4);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_16);
x_83 = l_Lean_Syntax_isOfKind(x_16, x_13);
if (x_83 == 0)
{
x_26 = x_83;
goto block_82;
}
else
{
x_26 = x_6;
goto block_82;
}
block_25:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_18, x_3, x_19);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
block_82:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(2u);
if (x_26 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_31, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_19 = x_33;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_16, x_34);
x_36 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_36);
lean_inc(x_35);
x_38 = l_Lean_Syntax_isOfKind(x_35, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_39, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_19 = x_41;
goto block_25;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Syntax_getArg(x_35, x_34);
lean_dec(x_35);
x_43 = l_Lean_Syntax_matchesNull(x_42, x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_44 = lean_box(0);
x_45 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_44, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_19 = x_46;
goto block_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = l_Lean_Syntax_getArg(x_16, x_28);
lean_dec(x_16);
x_48 = lean_mk_string_unchecked("Attr", 4, 4);
x_49 = lean_mk_string_unchecked("simple", 6, 6);
x_50 = l_Lean_Name_mkStr4(x_7, x_8, x_48, x_49);
lean_inc(x_47);
x_51 = l_Lean_Syntax_isOfKind(x_47, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
x_52 = lean_box(0);
x_53 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_52, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_19 = x_54;
goto block_25;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Syntax_getArg(x_47, x_34);
lean_inc(x_55);
x_56 = l_Lean_Syntax_isOfKind(x_55, x_14);
lean_dec(x_14);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_37);
lean_dec(x_13);
x_57 = lean_box(0);
x_58 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_57, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_19 = x_59;
goto block_25;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Syntax_getArg(x_47, x_28);
lean_dec(x_47);
x_61 = l_Lean_Syntax_matchesNull(x_60, x_34);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_13);
x_62 = lean_box(0);
x_63 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_62, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_19 = x_64;
goto block_25;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = l_Lean_Syntax_getId(x_55);
x_66 = lean_erase_macro_scopes(x_65);
x_67 = lean_mk_string_unchecked("inherit_doc", 11, 11);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = lean_name_eq(x_66, x_68);
lean_dec(x_68);
lean_dec(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_13);
x_70 = lean_box(0);
x_71 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_70, x_29, x_30);
lean_dec(x_29);
lean_dec(x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_19 = x_72;
goto block_25;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_29);
lean_dec(x_4);
x_73 = l_Lean_SourceInfo_fromRef(x_27, x_15);
x_74 = lean_mk_string_unchecked("null", 4, 4);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = l_Array_mkArray0(lean_box(0));
lean_inc(x_75);
lean_inc(x_73);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_73);
x_78 = l_Lean_Syntax_node1(x_73, x_37, x_77);
lean_inc(x_1);
lean_inc(x_73);
x_79 = l_Lean_Syntax_node1(x_73, x_75, x_1);
lean_inc(x_73);
x_80 = l_Lean_Syntax_node2(x_73, x_50, x_55, x_79);
x_81 = l_Lean_Syntax_node2(x_73, x_13, x_78, x_80);
x_19 = x_81;
goto block_25;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; uint8_t x_82; 
x_6 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_6);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Name_mkStr1(x_7);
x_15 = l_Lean_Syntax_getArg(x_1, x_12);
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_box(0);
lean_inc(x_4);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_16);
x_82 = l_Lean_Syntax_isOfKind(x_16, x_11);
if (x_82 == 0)
{
x_25 = x_82;
goto block_81;
}
else
{
x_25 = x_5;
goto block_81;
}
block_24:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_13);
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_18, x_3, x_19);
x_3 = x_21;
x_4 = x_22;
goto _start;
}
block_81:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_unsigned_to_nat(2u);
if (x_25 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_29, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Syntax_getArg(x_16, x_12);
x_33 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_33);
lean_inc(x_32);
x_35 = l_Lean_Syntax_isOfKind(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_36 = lean_box(0);
x_37 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_36, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_19 = x_38;
goto block_24;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Syntax_getArg(x_32, x_12);
lean_dec(x_32);
x_40 = l_Lean_Syntax_matchesNull(x_39, x_12);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_41 = lean_box(0);
x_42 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_41, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_19 = x_43;
goto block_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = l_Lean_Syntax_getArg(x_16, x_13);
lean_dec(x_16);
x_45 = lean_mk_string_unchecked("Attr", 4, 4);
x_46 = lean_mk_string_unchecked("simple", 6, 6);
x_47 = l_Lean_Name_mkStr4(x_8, x_9, x_45, x_46);
lean_inc(x_44);
x_48 = l_Lean_Syntax_isOfKind(x_44, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_49 = lean_box(0);
x_50 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_49, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_19 = x_51;
goto block_24;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Syntax_getArg(x_44, x_12);
lean_inc(x_52);
x_53 = l_Lean_Syntax_isOfKind(x_52, x_14);
lean_dec(x_14);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_11);
x_54 = lean_box(0);
x_55 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_54, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_19 = x_56;
goto block_24;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Syntax_getArg(x_44, x_13);
lean_dec(x_44);
x_58 = l_Lean_Syntax_matchesNull(x_57, x_12);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_11);
x_59 = lean_box(0);
x_60 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_59, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_19 = x_61;
goto block_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = l_Lean_Syntax_getId(x_52);
x_63 = lean_erase_macro_scopes(x_62);
x_64 = lean_mk_string_unchecked("inherit_doc", 11, 11);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = lean_name_eq(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_11);
x_67 = lean_box(0);
x_68 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_4, x_3, x_67, x_27, x_28);
lean_dec(x_27);
lean_dec(x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_19 = x_69;
goto block_24;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_27);
lean_dec(x_4);
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_72 = l_Lean_SourceInfo_fromRef(x_26, x_71);
x_73 = lean_mk_string_unchecked("null", 4, 4);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = l_Array_mkArray0(lean_box(0));
lean_inc(x_74);
lean_inc(x_72);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_72);
x_77 = l_Lean_Syntax_node1(x_72, x_34, x_76);
lean_inc(x_72);
x_78 = l_Lean_Syntax_node1(x_72, x_74, x_15);
lean_inc(x_72);
x_79 = l_Lean_Syntax_node2(x_72, x_47, x_52, x_78);
x_80 = l_Lean_Syntax_node2(x_72, x_11, x_77, x_79);
x_19 = x_80;
goto block_24;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_mk_string_unchecked("ident", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_mk_string_unchecked(",", 1, 1);
x_20 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_21 = lean_array_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(x_1, x_21, x_23, x_20);
x_25 = l_Lean_Syntax_TSepArray_ofElems(x_18, x_19, x_24);
lean_dec(x_24);
lean_dec(x_18);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_mk_string_unchecked(",", 1, 1);
x_31 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_32 = lean_array_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(x_1, x_32, x_34, x_31);
x_36 = l_Lean_Syntax_TSepArray_ofElems(x_29, x_30, x_35);
lean_dec(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
x_40 = lean_mk_string_unchecked("ident", 5, 5);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = l_Lean_Syntax_isOfKind(x_39, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_45 = lean_box(0);
x_46 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_47 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_mk_string_unchecked(",", 1, 1);
x_50 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_51 = lean_array_size(x_50);
x_52 = lean_usize_of_nat(x_38);
x_53 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(x_1, x_51, x_52, x_50);
lean_dec(x_1);
x_54 = l_Lean_Syntax_TSepArray_ofElems(x_48, x_49, x_53);
lean_dec(x_53);
lean_dec(x_48);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_57 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_mk_string_unchecked(",", 1, 1);
x_60 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_61 = lean_array_size(x_60);
x_62 = lean_usize_of_nat(x_38);
x_63 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(x_1, x_61, x_62, x_60);
lean_dec(x_1);
x_64 = l_Lean_Syntax_TSepArray_ofElems(x_58, x_59, x_63);
lean_dec(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___lam__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Parser", 6, 6);
x_48 = lean_mk_string_unchecked("Command", 7, 7);
x_49 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_17);
lean_inc(x_16);
x_50 = l_Lean_Name_mkStr4(x_16, x_17, x_48, x_49);
lean_inc(x_1);
x_51 = l_Lean_Syntax_isOfKind(x_1, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_mk_string_unchecked("str", 3, 3);
x_53 = l_Lean_Name_mkStr1(x_52);
lean_inc(x_1);
x_54 = l_Lean_Syntax_isOfKind(x_1, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_55 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_2, 5);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_SourceInfo_fromRef(x_56, x_51);
lean_dec(x_56);
x_58 = lean_mk_string_unchecked("Syntax", 6, 6);
x_59 = lean_mk_string_unchecked("atom", 4, 4);
x_60 = l_Lean_Name_mkStr4(x_16, x_17, x_58, x_59);
x_61 = l_Lean_Syntax_node1(x_57, x_60, x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getArg(x_1, x_63);
x_65 = lean_mk_string_unchecked("ident", 5, 5);
x_66 = l_Lean_Name_mkStr1(x_65);
x_67 = l_Lean_Syntax_isOfKind(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_68 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Syntax_getArg(x_1, x_69);
lean_dec(x_1);
x_71 = l_Lean_Syntax_isNone(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
lean_inc(x_70);
x_72 = l_Lean_Syntax_matchesNull(x_70, x_69);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_70);
lean_dec(x_17);
lean_dec(x_16);
x_73 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = l_Lean_Syntax_getArg(x_70, x_63);
lean_dec(x_70);
x_75 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_17);
lean_inc(x_16);
x_76 = l_Lean_Name_mkStr3(x_16, x_17, x_75);
lean_inc(x_74);
x_77 = l_Lean_Syntax_isOfKind(x_74, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_17);
lean_dec(x_16);
x_78 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Syntax_getArg(x_74, x_69);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_18 = x_80;
x_19 = x_2;
x_20 = x_3;
goto block_47;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_70);
x_81 = lean_box(0);
x_18 = x_81;
x_19 = x_2;
x_20 = x_3;
goto block_47;
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Array_append(lean_box(0), x_9, x_10);
lean_dec(x_10);
lean_inc(x_8);
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_Syntax_node2(x_8, x_7, x_5, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
block_47:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_19, 5);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_SourceInfo_fromRef(x_21, x_23);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_mk_string_unchecked("Syntax", 6, 6);
x_28 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_17);
lean_inc(x_16);
x_29 = l_Lean_Name_mkStr4(x_16, x_17, x_27, x_28);
x_30 = lean_mk_string_unchecked("term", 4, 4);
lean_inc(x_30);
x_31 = l_String_toSubstring_x27(x_30);
x_32 = l_Lean_Name_mkStr1(x_30);
x_33 = l_Lean_addMacroScope(x_26, x_32, x_25);
x_34 = lean_box(0);
lean_inc(x_24);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_16);
x_39 = l_Array_empty(lean_box(0));
x_4 = x_37;
x_5 = x_35;
x_6 = x_20;
x_7 = x_29;
x_8 = x_24;
x_9 = x_38;
x_10 = x_39;
goto block_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_mk_string_unchecked("precedence", 10, 10);
x_42 = l_Lean_Name_mkStr3(x_16, x_17, x_41);
x_43 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_24);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_24);
x_45 = l_Lean_Syntax_node2(x_24, x_42, x_44, x_40);
x_46 = l_Array_mkArray1___redArg(x_45);
x_4 = x_37;
x_5 = x_35;
x_6 = x_20;
x_7 = x_29;
x_8 = x_24;
x_9 = x_38;
x_10 = x_46;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("identPrec", 9, 9);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = lean_name_eq(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_mk_string_unchecked("str", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_name_eq(x_4, x_12);
lean_dec(x_12);
lean_dec(x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_strLitToPattern(x_1, x_2, x_3);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_16 = lean_mk_string_unchecked("term", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = l_Lean_Syntax_mkAntiquotNode(x_17, x_19, x_18, x_20, x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNotationItemIntoPattern(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_getHeadInfo(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Syntax_getTailInfo(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 2);
lean_dec(x_14);
x_15 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 2);
x_18 = lean_ctor_get(x_15, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 0, x_4);
x_21 = l_Lean_Syntax_setHeadInfo(x_2, x_15);
lean_ctor_set(x_9, 2, x_17);
x_22 = l_Lean_Syntax_setTailInfo(x_21, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set(x_24, 3, x_8);
x_25 = l_Lean_Syntax_setHeadInfo(x_2, x_24);
lean_ctor_set(x_9, 2, x_23);
x_26 = l_Lean_Syntax_setTailInfo(x_25, x_9);
return x_26;
}
}
else
{
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_30 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 4, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
x_34 = l_Lean_Syntax_setHeadInfo(x_2, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_29);
x_36 = l_Lean_Syntax_setTailInfo(x_34, x_35);
return x_36;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_2;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_9 = l_Lean_Elab_Command_removeParentheses(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("paren", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_array_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_14, x_16, x_13, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 2, x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; size_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = lean_array_size(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_usize_of_nat(x_31);
x_33 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_30, x_32, x_29, x_2, x_3);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_27);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_inc(x_2);
lean_inc(x_45);
x_46 = l_Lean_Elab_Term_expandCDot_x3f(x_45, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
x_49 = x_45;
goto block_58;
}
else
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
lean_dec(x_47);
x_49 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_50; 
x_50 = l_Lean_Elab_Command_removeParentheses(x_49, x_2, x_48);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_52);
lean_dec(x_1);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_54);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_dec(x_1);
return x_50;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
return x_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_46, 0);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_46);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_9);
x_10 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_8, x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_5, x_17);
x_5 = x_18;
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_18; lean_object* x_19; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_box(0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lean_Syntax_isAntiquot(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_inc(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_18 = x_35;
x_19 = x_34;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Syntax_getAntiquotTerm(x_2);
x_37 = l_Lean_Syntax_getId(x_36);
lean_dec(x_36);
x_38 = l_Lean_NameSet_contains(x_32, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_NameSet_insert(x_32, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_18 = x_41;
x_19 = x_40;
goto block_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_2);
x_42 = lean_box(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_32);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
block_17:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_1, x_4, x_6, x_9, x_11, x_8);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
return x_16;
}
}
block_30:
{
if (lean_obj_tag(x_2) == 1)
{
lean_dec(x_18);
if (x_1 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_dec(x_2);
x_5 = x_19;
x_6 = x_20;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("choice", 6, 6);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_name_eq(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
x_5 = x_19;
x_6 = x_22;
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_instInhabitedSyntax;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get(x_26, x_22, x_27);
lean_dec(x_22);
x_2 = x_28;
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_box(0);
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_20);
x_21 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_5, x_18, x_20, x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_7 = x_22;
goto block_17;
block_17:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_box(0);
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_20);
x_21 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_5, x_18, x_20, x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_7 = x_22;
goto block_17;
block_17:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(x_1, x_2, x_13, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_array_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(x_1, x_5, x_7, x_4);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_635 = lean_mk_string_unchecked("Lean", 4, 4);
x_636 = lean_mk_string_unchecked("Parser", 6, 6);
x_637 = lean_mk_string_unchecked("Term", 4, 4);
x_638 = lean_mk_string_unchecked("app", 3, 3);
x_639 = l_Lean_Name_mkStr4(x_635, x_636, x_637, x_638);
lean_inc(x_3);
x_640 = l_Lean_Syntax_isOfKind(x_3, x_639);
lean_dec(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; uint8_t x_643; 
x_641 = lean_mk_string_unchecked("ident", 5, 5);
x_642 = l_Lean_Name_mkStr1(x_641);
lean_inc(x_3);
x_643 = l_Lean_Syntax_isOfKind(x_3, x_642);
lean_dec(x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_644 = lean_box(0);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_5);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; 
x_646 = lean_unsigned_to_nat(0u);
x_647 = lean_mk_empty_array_with_capacity(x_646);
x_10 = x_3;
x_11 = x_647;
x_12 = x_4;
x_13 = x_5;
goto block_634;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; 
x_648 = lean_unsigned_to_nat(0u);
x_649 = l_Lean_Syntax_getArg(x_3, x_648);
x_650 = lean_mk_string_unchecked("ident", 5, 5);
x_651 = l_Lean_Name_mkStr1(x_650);
lean_inc(x_649);
x_652 = l_Lean_Syntax_isOfKind(x_649, x_651);
lean_dec(x_651);
if (x_652 == 0)
{
lean_object* x_653; lean_object* x_654; 
lean_dec(x_649);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_653 = lean_box(0);
x_654 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_5);
return x_654;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_unsigned_to_nat(1u);
x_656 = l_Lean_Syntax_getArg(x_3, x_655);
lean_dec(x_3);
x_657 = l_Lean_Syntax_getArgs(x_656);
lean_dec(x_656);
x_10 = x_649;
x_11 = x_657;
x_12 = x_4;
x_13 = x_5;
goto block_634;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_634:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
lean_inc(x_12);
x_15 = l_Lean_Macro_resolveGlobalName(x_14, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_6 = x_17;
goto block_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_dec(x_26);
x_27 = lean_array_size(x_11);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_usize_of_nat(x_28);
lean_inc(x_12);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_27, x_29, x_11, x_12, x_23);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_34 = lean_ctor_get(x_12, 5);
lean_inc(x_34);
x_35 = l_Lean_SourceInfo_fromRef(x_34, x_33);
lean_dec(x_34);
x_36 = lean_ctor_get(x_12, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_mk_string_unchecked("ident", 5, 5);
x_39 = lean_mk_string_unchecked("antiquot", 8, 8);
lean_inc(x_38);
x_40 = l_Lean_Name_mkStr2(x_38, x_39);
x_41 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_35);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_41);
lean_ctor_set(x_18, 0, x_35);
x_42 = lean_mk_string_unchecked("null", 4, 4);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = l_Array_mkArray0(lean_box(0));
lean_inc(x_43);
lean_inc(x_35);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_mk_string_unchecked("f", 1, 1);
lean_inc(x_46);
x_47 = l_String_toSubstring_x27(x_46);
x_48 = l_Lean_Name_mkStr1(x_46);
lean_inc(x_36);
lean_inc(x_37);
x_49 = l_Lean_addMacroScope(x_37, x_48, x_36);
x_50 = lean_box(0);
lean_inc(x_35);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_35);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_35);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_38);
lean_inc(x_55);
lean_inc(x_35);
x_57 = l_Lean_Syntax_node2(x_35, x_53, x_55, x_56);
lean_inc(x_51);
lean_inc(x_45);
lean_inc(x_35);
x_58 = l_Lean_Syntax_node4(x_35, x_40, x_18, x_45, x_51, x_57);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Elab", 4, 4);
x_61 = lean_mk_string_unchecked("Command", 7, 7);
x_62 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_62);
lean_inc(x_59);
x_63 = l_Lean_Name_mkStr4(x_59, x_60, x_61, x_62);
x_64 = lean_mk_string_unchecked("Parser", 6, 6);
x_65 = lean_mk_string_unchecked("Term", 4, 4);
x_66 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_67 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_66);
x_68 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_35);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_35);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_71 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_70);
x_72 = lean_mk_string_unchecked("Attr", 4, 4);
x_73 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_64);
lean_inc(x_59);
x_74 = l_Lean_Name_mkStr4(x_59, x_64, x_72, x_73);
x_75 = lean_mk_string_unchecked("app_unexpander", 14, 14);
lean_inc(x_75);
x_76 = l_String_toSubstring_x27(x_75);
x_77 = l_Lean_Name_mkStr1(x_75);
lean_inc(x_36);
lean_inc(x_37);
x_78 = l_Lean_addMacroScope(x_37, x_77, x_36);
lean_inc(x_35);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_35);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_50);
x_80 = lean_mk_syntax_ident(x_25);
lean_inc(x_80);
lean_inc(x_43);
lean_inc(x_35);
x_81 = l_Lean_Syntax_node1(x_35, x_43, x_80);
lean_inc(x_35);
x_82 = l_Lean_Syntax_node2(x_35, x_74, x_79, x_81);
lean_inc(x_35);
x_83 = l_Lean_Syntax_node2(x_35, x_71, x_1, x_82);
lean_inc(x_43);
lean_inc(x_35);
x_84 = l_Lean_Syntax_node1(x_35, x_43, x_83);
x_85 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_35);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_35);
x_87 = l_Lean_Syntax_node3(x_35, x_67, x_69, x_84, x_86);
lean_inc(x_43);
lean_inc(x_35);
x_88 = l_Lean_Syntax_node1(x_35, x_43, x_87);
lean_inc(x_35);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_35);
lean_ctor_set(x_89, 1, x_62);
x_90 = lean_mk_string_unchecked("unexpand", 8, 8);
lean_inc(x_90);
x_91 = l_String_toSubstring_x27(x_90);
x_92 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_36);
lean_inc(x_37);
x_93 = l_Lean_addMacroScope(x_37, x_92, x_36);
lean_inc(x_35);
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_35);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_50);
lean_inc(x_43);
lean_inc(x_35);
x_95 = l_Lean_Syntax_node2(x_35, x_43, x_94, x_80);
x_96 = lean_mk_string_unchecked("Lean.PrettyPrinter.Unexpander", 29, 29);
x_97 = l_String_toSubstring_x27(x_96);
x_98 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_99 = lean_mk_string_unchecked("Unexpander", 10, 10);
lean_inc(x_59);
x_100 = l_Lean_Name_mkStr3(x_59, x_98, x_99);
lean_inc(x_36);
lean_inc(x_100);
lean_inc(x_37);
x_101 = l_Lean_addMacroScope(x_37, x_100, x_36);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_19);
lean_ctor_set(x_16, 1, x_50);
lean_ctor_set(x_16, 0, x_102);
lean_inc(x_35);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_35);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_16);
x_104 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_35);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_35);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_106);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_107 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_106);
lean_inc(x_35);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_35);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_110 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_109);
x_111 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_112 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_111);
x_113 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_35);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_116 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_115);
x_117 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_35);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Syntax_mkApp(x_58, x_32);
x_120 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_35);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_35);
lean_ctor_set(x_121, 1, x_120);
lean_inc(x_121);
lean_inc(x_118);
lean_inc(x_116);
lean_inc(x_35);
x_122 = l_Lean_Syntax_node3(x_35, x_116, x_118, x_119, x_121);
lean_inc(x_43);
lean_inc(x_35);
x_123 = l_Lean_Syntax_node1(x_35, x_43, x_122);
lean_inc(x_43);
lean_inc(x_35);
x_124 = l_Lean_Syntax_node1(x_35, x_43, x_123);
x_125 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_35);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_35);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_128 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_127);
x_129 = lean_mk_string_unchecked("withRef", 7, 7);
lean_inc(x_129);
x_130 = l_String_toSubstring_x27(x_129);
lean_inc(x_129);
x_131 = l_Lean_Name_mkStr1(x_129);
lean_inc(x_36);
lean_inc(x_37);
x_132 = l_Lean_addMacroScope(x_37, x_131, x_36);
lean_inc(x_59);
x_133 = l_Lean_Name_mkStr2(x_59, x_129);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_19);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_50);
lean_inc(x_35);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_35);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_132);
lean_ctor_set(x_136, 3, x_135);
lean_inc(x_121);
lean_inc(x_35);
x_137 = l_Lean_Syntax_node3(x_35, x_116, x_118, x_2, x_121);
lean_inc(x_43);
lean_inc(x_35);
x_138 = l_Lean_Syntax_node2(x_35, x_43, x_51, x_137);
lean_inc(x_128);
lean_inc(x_35);
x_139 = l_Lean_Syntax_node2(x_35, x_128, x_136, x_138);
lean_inc(x_126);
lean_inc(x_114);
lean_inc(x_112);
lean_inc(x_35);
x_140 = l_Lean_Syntax_node4(x_35, x_112, x_114, x_124, x_126, x_139);
x_141 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
x_142 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_141);
x_143 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_35);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_35);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_35);
x_145 = l_Lean_Syntax_node1(x_35, x_142, x_144);
lean_inc(x_43);
lean_inc(x_35);
x_146 = l_Lean_Syntax_node1(x_35, x_43, x_145);
lean_inc(x_43);
lean_inc(x_35);
x_147 = l_Lean_Syntax_node1(x_35, x_43, x_146);
x_148 = lean_mk_string_unchecked("throw", 5, 5);
lean_inc(x_148);
x_149 = l_String_toSubstring_x27(x_148);
lean_inc(x_148);
x_150 = l_Lean_Name_mkStr1(x_148);
x_151 = l_Lean_addMacroScope(x_37, x_150, x_36);
x_152 = lean_mk_string_unchecked("MonadExcept", 11, 11);
x_153 = l_Lean_Name_mkStr2(x_152, x_148);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_19);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_50);
lean_inc(x_35);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_35);
lean_ctor_set(x_156, 1, x_149);
lean_ctor_set(x_156, 2, x_151);
lean_ctor_set(x_156, 3, x_155);
x_157 = lean_mk_string_unchecked("tuple", 5, 5);
x_158 = l_Lean_Name_mkStr4(x_59, x_64, x_65, x_157);
x_159 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_35);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_35);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_45);
lean_inc(x_35);
x_161 = l_Lean_Syntax_node3(x_35, x_158, x_160, x_45, x_121);
lean_inc(x_43);
lean_inc(x_35);
x_162 = l_Lean_Syntax_node1(x_35, x_43, x_161);
lean_inc(x_35);
x_163 = l_Lean_Syntax_node2(x_35, x_128, x_156, x_162);
lean_inc(x_35);
x_164 = l_Lean_Syntax_node4(x_35, x_112, x_114, x_147, x_126, x_163);
lean_inc(x_35);
x_165 = l_Lean_Syntax_node2(x_35, x_43, x_140, x_164);
lean_inc(x_35);
x_166 = l_Lean_Syntax_node1(x_35, x_110, x_165);
lean_inc(x_35);
x_167 = l_Lean_Syntax_node2(x_35, x_107, x_108, x_166);
x_168 = l_Lean_Syntax_node8(x_35, x_63, x_45, x_88, x_89, x_95, x_55, x_103, x_105, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_30, 0, x_169);
return x_30;
}
else
{
lean_object* x_170; 
lean_dec(x_32);
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_box(0);
lean_ctor_set(x_30, 0, x_170);
return x_30;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_30, 0);
x_172 = lean_ctor_get(x_30, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_30);
x_173 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_174 = lean_ctor_get(x_12, 5);
lean_inc(x_174);
x_175 = l_Lean_SourceInfo_fromRef(x_174, x_173);
lean_dec(x_174);
x_176 = lean_ctor_get(x_12, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_12, 1);
lean_inc(x_177);
lean_dec(x_12);
x_178 = lean_mk_string_unchecked("ident", 5, 5);
x_179 = lean_mk_string_unchecked("antiquot", 8, 8);
lean_inc(x_178);
x_180 = l_Lean_Name_mkStr2(x_178, x_179);
x_181 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_175);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_181);
lean_ctor_set(x_18, 0, x_175);
x_182 = lean_mk_string_unchecked("null", 4, 4);
x_183 = l_Lean_Name_mkStr1(x_182);
x_184 = l_Array_mkArray0(lean_box(0));
lean_inc(x_183);
lean_inc(x_175);
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_175);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_184);
x_186 = lean_mk_string_unchecked("f", 1, 1);
lean_inc(x_186);
x_187 = l_String_toSubstring_x27(x_186);
x_188 = l_Lean_Name_mkStr1(x_186);
lean_inc(x_176);
lean_inc(x_177);
x_189 = l_Lean_addMacroScope(x_177, x_188, x_176);
x_190 = lean_box(0);
lean_inc(x_175);
x_191 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_191, 0, x_175);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_189);
lean_ctor_set(x_191, 3, x_190);
x_192 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_193 = l_Lean_Name_mkStr1(x_192);
x_194 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_175);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_175);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_175);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_175);
lean_ctor_set(x_196, 1, x_178);
lean_inc(x_195);
lean_inc(x_175);
x_197 = l_Lean_Syntax_node2(x_175, x_193, x_195, x_196);
lean_inc(x_191);
lean_inc(x_185);
lean_inc(x_175);
x_198 = l_Lean_Syntax_node4(x_175, x_180, x_18, x_185, x_191, x_197);
x_199 = lean_mk_string_unchecked("Lean", 4, 4);
x_200 = lean_mk_string_unchecked("Elab", 4, 4);
x_201 = lean_mk_string_unchecked("Command", 7, 7);
x_202 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_202);
lean_inc(x_199);
x_203 = l_Lean_Name_mkStr4(x_199, x_200, x_201, x_202);
x_204 = lean_mk_string_unchecked("Parser", 6, 6);
x_205 = lean_mk_string_unchecked("Term", 4, 4);
x_206 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_207 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_206);
x_208 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_175);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_175);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_211 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_210);
x_212 = lean_mk_string_unchecked("Attr", 4, 4);
x_213 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_204);
lean_inc(x_199);
x_214 = l_Lean_Name_mkStr4(x_199, x_204, x_212, x_213);
x_215 = lean_mk_string_unchecked("app_unexpander", 14, 14);
lean_inc(x_215);
x_216 = l_String_toSubstring_x27(x_215);
x_217 = l_Lean_Name_mkStr1(x_215);
lean_inc(x_176);
lean_inc(x_177);
x_218 = l_Lean_addMacroScope(x_177, x_217, x_176);
lean_inc(x_175);
x_219 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_219, 0, x_175);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_190);
x_220 = lean_mk_syntax_ident(x_25);
lean_inc(x_220);
lean_inc(x_183);
lean_inc(x_175);
x_221 = l_Lean_Syntax_node1(x_175, x_183, x_220);
lean_inc(x_175);
x_222 = l_Lean_Syntax_node2(x_175, x_214, x_219, x_221);
lean_inc(x_175);
x_223 = l_Lean_Syntax_node2(x_175, x_211, x_1, x_222);
lean_inc(x_183);
lean_inc(x_175);
x_224 = l_Lean_Syntax_node1(x_175, x_183, x_223);
x_225 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_175);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_175);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_175);
x_227 = l_Lean_Syntax_node3(x_175, x_207, x_209, x_224, x_226);
lean_inc(x_183);
lean_inc(x_175);
x_228 = l_Lean_Syntax_node1(x_175, x_183, x_227);
lean_inc(x_175);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_175);
lean_ctor_set(x_229, 1, x_202);
x_230 = lean_mk_string_unchecked("unexpand", 8, 8);
lean_inc(x_230);
x_231 = l_String_toSubstring_x27(x_230);
x_232 = l_Lean_Name_mkStr1(x_230);
lean_inc(x_176);
lean_inc(x_177);
x_233 = l_Lean_addMacroScope(x_177, x_232, x_176);
lean_inc(x_175);
x_234 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_234, 0, x_175);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_233);
lean_ctor_set(x_234, 3, x_190);
lean_inc(x_183);
lean_inc(x_175);
x_235 = l_Lean_Syntax_node2(x_175, x_183, x_234, x_220);
x_236 = lean_mk_string_unchecked("Lean.PrettyPrinter.Unexpander", 29, 29);
x_237 = l_String_toSubstring_x27(x_236);
x_238 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_239 = lean_mk_string_unchecked("Unexpander", 10, 10);
lean_inc(x_199);
x_240 = l_Lean_Name_mkStr3(x_199, x_238, x_239);
lean_inc(x_176);
lean_inc(x_240);
lean_inc(x_177);
x_241 = l_Lean_addMacroScope(x_177, x_240, x_176);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_19);
lean_ctor_set(x_16, 1, x_190);
lean_ctor_set(x_16, 0, x_242);
lean_inc(x_175);
x_243 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_243, 0, x_175);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_241);
lean_ctor_set(x_243, 3, x_16);
x_244 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_175);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_175);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_246);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_247 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_246);
lean_inc(x_175);
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_175);
lean_ctor_set(x_248, 1, x_246);
x_249 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_250 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_249);
x_251 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_252 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_251);
x_253 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_175);
x_254 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_254, 0, x_175);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_256 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_255);
x_257 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_175);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_175);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Syntax_mkApp(x_198, x_171);
x_260 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_175);
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_175);
lean_ctor_set(x_261, 1, x_260);
lean_inc(x_261);
lean_inc(x_258);
lean_inc(x_256);
lean_inc(x_175);
x_262 = l_Lean_Syntax_node3(x_175, x_256, x_258, x_259, x_261);
lean_inc(x_183);
lean_inc(x_175);
x_263 = l_Lean_Syntax_node1(x_175, x_183, x_262);
lean_inc(x_183);
lean_inc(x_175);
x_264 = l_Lean_Syntax_node1(x_175, x_183, x_263);
x_265 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_175);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_175);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_268 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_267);
x_269 = lean_mk_string_unchecked("withRef", 7, 7);
lean_inc(x_269);
x_270 = l_String_toSubstring_x27(x_269);
lean_inc(x_269);
x_271 = l_Lean_Name_mkStr1(x_269);
lean_inc(x_176);
lean_inc(x_177);
x_272 = l_Lean_addMacroScope(x_177, x_271, x_176);
lean_inc(x_199);
x_273 = l_Lean_Name_mkStr2(x_199, x_269);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_19);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_190);
lean_inc(x_175);
x_276 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_276, 0, x_175);
lean_ctor_set(x_276, 1, x_270);
lean_ctor_set(x_276, 2, x_272);
lean_ctor_set(x_276, 3, x_275);
lean_inc(x_261);
lean_inc(x_175);
x_277 = l_Lean_Syntax_node3(x_175, x_256, x_258, x_2, x_261);
lean_inc(x_183);
lean_inc(x_175);
x_278 = l_Lean_Syntax_node2(x_175, x_183, x_191, x_277);
lean_inc(x_268);
lean_inc(x_175);
x_279 = l_Lean_Syntax_node2(x_175, x_268, x_276, x_278);
lean_inc(x_266);
lean_inc(x_254);
lean_inc(x_252);
lean_inc(x_175);
x_280 = l_Lean_Syntax_node4(x_175, x_252, x_254, x_264, x_266, x_279);
x_281 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
x_282 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_281);
x_283 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_175);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_175);
lean_ctor_set(x_284, 1, x_283);
lean_inc(x_175);
x_285 = l_Lean_Syntax_node1(x_175, x_282, x_284);
lean_inc(x_183);
lean_inc(x_175);
x_286 = l_Lean_Syntax_node1(x_175, x_183, x_285);
lean_inc(x_183);
lean_inc(x_175);
x_287 = l_Lean_Syntax_node1(x_175, x_183, x_286);
x_288 = lean_mk_string_unchecked("throw", 5, 5);
lean_inc(x_288);
x_289 = l_String_toSubstring_x27(x_288);
lean_inc(x_288);
x_290 = l_Lean_Name_mkStr1(x_288);
x_291 = l_Lean_addMacroScope(x_177, x_290, x_176);
x_292 = lean_mk_string_unchecked("MonadExcept", 11, 11);
x_293 = l_Lean_Name_mkStr2(x_292, x_288);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_19);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_190);
lean_inc(x_175);
x_296 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_296, 0, x_175);
lean_ctor_set(x_296, 1, x_289);
lean_ctor_set(x_296, 2, x_291);
lean_ctor_set(x_296, 3, x_295);
x_297 = lean_mk_string_unchecked("tuple", 5, 5);
x_298 = l_Lean_Name_mkStr4(x_199, x_204, x_205, x_297);
x_299 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_175);
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_175);
lean_ctor_set(x_300, 1, x_299);
lean_inc(x_185);
lean_inc(x_175);
x_301 = l_Lean_Syntax_node3(x_175, x_298, x_300, x_185, x_261);
lean_inc(x_183);
lean_inc(x_175);
x_302 = l_Lean_Syntax_node1(x_175, x_183, x_301);
lean_inc(x_175);
x_303 = l_Lean_Syntax_node2(x_175, x_268, x_296, x_302);
lean_inc(x_175);
x_304 = l_Lean_Syntax_node4(x_175, x_252, x_254, x_287, x_266, x_303);
lean_inc(x_175);
x_305 = l_Lean_Syntax_node2(x_175, x_183, x_280, x_304);
lean_inc(x_175);
x_306 = l_Lean_Syntax_node1(x_175, x_250, x_305);
lean_inc(x_175);
x_307 = l_Lean_Syntax_node2(x_175, x_247, x_248, x_306);
x_308 = l_Lean_Syntax_node8(x_175, x_203, x_185, x_228, x_229, x_235, x_195, x_243, x_245, x_307);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_172);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_171);
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_311 = lean_box(0);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_172);
return x_312;
}
}
}
else
{
uint8_t x_313; 
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_30);
if (x_313 == 0)
{
return x_30;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_30, 0);
x_315 = lean_ctor_get(x_30, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_30);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
lean_object* x_317; size_t x_318; lean_object* x_319; size_t x_320; lean_object* x_321; 
x_317 = lean_ctor_get(x_18, 0);
lean_inc(x_317);
lean_dec(x_18);
x_318 = lean_array_size(x_11);
x_319 = lean_unsigned_to_nat(0u);
x_320 = lean_usize_of_nat(x_319);
lean_inc(x_12);
x_321 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_318, x_320, x_11, x_12, x_23);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
 x_324 = lean_box(0);
}
x_325 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_322);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_326 = lean_ctor_get(x_12, 5);
lean_inc(x_326);
x_327 = l_Lean_SourceInfo_fromRef(x_326, x_325);
lean_dec(x_326);
x_328 = lean_ctor_get(x_12, 2);
lean_inc(x_328);
x_329 = lean_ctor_get(x_12, 1);
lean_inc(x_329);
lean_dec(x_12);
x_330 = lean_mk_string_unchecked("ident", 5, 5);
x_331 = lean_mk_string_unchecked("antiquot", 8, 8);
lean_inc(x_330);
x_332 = l_Lean_Name_mkStr2(x_330, x_331);
x_333 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_327);
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_mk_string_unchecked("null", 4, 4);
x_336 = l_Lean_Name_mkStr1(x_335);
x_337 = l_Array_mkArray0(lean_box(0));
lean_inc(x_336);
lean_inc(x_327);
x_338 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_338, 0, x_327);
lean_ctor_set(x_338, 1, x_336);
lean_ctor_set(x_338, 2, x_337);
x_339 = lean_mk_string_unchecked("f", 1, 1);
lean_inc(x_339);
x_340 = l_String_toSubstring_x27(x_339);
x_341 = l_Lean_Name_mkStr1(x_339);
lean_inc(x_328);
lean_inc(x_329);
x_342 = l_Lean_addMacroScope(x_329, x_341, x_328);
x_343 = lean_box(0);
lean_inc(x_327);
x_344 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_344, 0, x_327);
lean_ctor_set(x_344, 1, x_340);
lean_ctor_set(x_344, 2, x_342);
lean_ctor_set(x_344, 3, x_343);
x_345 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_346 = l_Lean_Name_mkStr1(x_345);
x_347 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_327);
x_348 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_348, 0, x_327);
lean_ctor_set(x_348, 1, x_347);
lean_inc(x_327);
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_327);
lean_ctor_set(x_349, 1, x_330);
lean_inc(x_348);
lean_inc(x_327);
x_350 = l_Lean_Syntax_node2(x_327, x_346, x_348, x_349);
lean_inc(x_344);
lean_inc(x_338);
lean_inc(x_327);
x_351 = l_Lean_Syntax_node4(x_327, x_332, x_334, x_338, x_344, x_350);
x_352 = lean_mk_string_unchecked("Lean", 4, 4);
x_353 = lean_mk_string_unchecked("Elab", 4, 4);
x_354 = lean_mk_string_unchecked("Command", 7, 7);
x_355 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_355);
lean_inc(x_352);
x_356 = l_Lean_Name_mkStr4(x_352, x_353, x_354, x_355);
x_357 = lean_mk_string_unchecked("Parser", 6, 6);
x_358 = lean_mk_string_unchecked("Term", 4, 4);
x_359 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_360 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_359);
x_361 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_327);
x_362 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_362, 0, x_327);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_364 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_363);
x_365 = lean_mk_string_unchecked("Attr", 4, 4);
x_366 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_357);
lean_inc(x_352);
x_367 = l_Lean_Name_mkStr4(x_352, x_357, x_365, x_366);
x_368 = lean_mk_string_unchecked("app_unexpander", 14, 14);
lean_inc(x_368);
x_369 = l_String_toSubstring_x27(x_368);
x_370 = l_Lean_Name_mkStr1(x_368);
lean_inc(x_328);
lean_inc(x_329);
x_371 = l_Lean_addMacroScope(x_329, x_370, x_328);
lean_inc(x_327);
x_372 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_372, 0, x_327);
lean_ctor_set(x_372, 1, x_369);
lean_ctor_set(x_372, 2, x_371);
lean_ctor_set(x_372, 3, x_343);
x_373 = lean_mk_syntax_ident(x_317);
lean_inc(x_373);
lean_inc(x_336);
lean_inc(x_327);
x_374 = l_Lean_Syntax_node1(x_327, x_336, x_373);
lean_inc(x_327);
x_375 = l_Lean_Syntax_node2(x_327, x_367, x_372, x_374);
lean_inc(x_327);
x_376 = l_Lean_Syntax_node2(x_327, x_364, x_1, x_375);
lean_inc(x_336);
lean_inc(x_327);
x_377 = l_Lean_Syntax_node1(x_327, x_336, x_376);
x_378 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_327);
x_379 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_379, 0, x_327);
lean_ctor_set(x_379, 1, x_378);
lean_inc(x_327);
x_380 = l_Lean_Syntax_node3(x_327, x_360, x_362, x_377, x_379);
lean_inc(x_336);
lean_inc(x_327);
x_381 = l_Lean_Syntax_node1(x_327, x_336, x_380);
lean_inc(x_327);
x_382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_382, 0, x_327);
lean_ctor_set(x_382, 1, x_355);
x_383 = lean_mk_string_unchecked("unexpand", 8, 8);
lean_inc(x_383);
x_384 = l_String_toSubstring_x27(x_383);
x_385 = l_Lean_Name_mkStr1(x_383);
lean_inc(x_328);
lean_inc(x_329);
x_386 = l_Lean_addMacroScope(x_329, x_385, x_328);
lean_inc(x_327);
x_387 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_387, 0, x_327);
lean_ctor_set(x_387, 1, x_384);
lean_ctor_set(x_387, 2, x_386);
lean_ctor_set(x_387, 3, x_343);
lean_inc(x_336);
lean_inc(x_327);
x_388 = l_Lean_Syntax_node2(x_327, x_336, x_387, x_373);
x_389 = lean_mk_string_unchecked("Lean.PrettyPrinter.Unexpander", 29, 29);
x_390 = l_String_toSubstring_x27(x_389);
x_391 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_392 = lean_mk_string_unchecked("Unexpander", 10, 10);
lean_inc(x_352);
x_393 = l_Lean_Name_mkStr3(x_352, x_391, x_392);
lean_inc(x_328);
lean_inc(x_393);
lean_inc(x_329);
x_394 = l_Lean_addMacroScope(x_329, x_393, x_328);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_19);
lean_ctor_set(x_16, 1, x_343);
lean_ctor_set(x_16, 0, x_395);
lean_inc(x_327);
x_396 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_396, 0, x_327);
lean_ctor_set(x_396, 1, x_390);
lean_ctor_set(x_396, 2, x_394);
lean_ctor_set(x_396, 3, x_16);
x_397 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_327);
x_398 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_398, 0, x_327);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_399);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_400 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_399);
lean_inc(x_327);
x_401 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_401, 0, x_327);
lean_ctor_set(x_401, 1, x_399);
x_402 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_403 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_402);
x_404 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_405 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_404);
x_406 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_327);
x_407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_407, 0, x_327);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_409 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_408);
x_410 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_327);
x_411 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_411, 0, x_327);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Syntax_mkApp(x_351, x_322);
x_413 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_327);
x_414 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_414, 0, x_327);
lean_ctor_set(x_414, 1, x_413);
lean_inc(x_414);
lean_inc(x_411);
lean_inc(x_409);
lean_inc(x_327);
x_415 = l_Lean_Syntax_node3(x_327, x_409, x_411, x_412, x_414);
lean_inc(x_336);
lean_inc(x_327);
x_416 = l_Lean_Syntax_node1(x_327, x_336, x_415);
lean_inc(x_336);
lean_inc(x_327);
x_417 = l_Lean_Syntax_node1(x_327, x_336, x_416);
x_418 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_327);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_327);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_421 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_420);
x_422 = lean_mk_string_unchecked("withRef", 7, 7);
lean_inc(x_422);
x_423 = l_String_toSubstring_x27(x_422);
lean_inc(x_422);
x_424 = l_Lean_Name_mkStr1(x_422);
lean_inc(x_328);
lean_inc(x_329);
x_425 = l_Lean_addMacroScope(x_329, x_424, x_328);
lean_inc(x_352);
x_426 = l_Lean_Name_mkStr2(x_352, x_422);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_19);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_343);
lean_inc(x_327);
x_429 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_429, 0, x_327);
lean_ctor_set(x_429, 1, x_423);
lean_ctor_set(x_429, 2, x_425);
lean_ctor_set(x_429, 3, x_428);
lean_inc(x_414);
lean_inc(x_327);
x_430 = l_Lean_Syntax_node3(x_327, x_409, x_411, x_2, x_414);
lean_inc(x_336);
lean_inc(x_327);
x_431 = l_Lean_Syntax_node2(x_327, x_336, x_344, x_430);
lean_inc(x_421);
lean_inc(x_327);
x_432 = l_Lean_Syntax_node2(x_327, x_421, x_429, x_431);
lean_inc(x_419);
lean_inc(x_407);
lean_inc(x_405);
lean_inc(x_327);
x_433 = l_Lean_Syntax_node4(x_327, x_405, x_407, x_417, x_419, x_432);
x_434 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_352);
x_435 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_434);
x_436 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_327);
x_437 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_437, 0, x_327);
lean_ctor_set(x_437, 1, x_436);
lean_inc(x_327);
x_438 = l_Lean_Syntax_node1(x_327, x_435, x_437);
lean_inc(x_336);
lean_inc(x_327);
x_439 = l_Lean_Syntax_node1(x_327, x_336, x_438);
lean_inc(x_336);
lean_inc(x_327);
x_440 = l_Lean_Syntax_node1(x_327, x_336, x_439);
x_441 = lean_mk_string_unchecked("throw", 5, 5);
lean_inc(x_441);
x_442 = l_String_toSubstring_x27(x_441);
lean_inc(x_441);
x_443 = l_Lean_Name_mkStr1(x_441);
x_444 = l_Lean_addMacroScope(x_329, x_443, x_328);
x_445 = lean_mk_string_unchecked("MonadExcept", 11, 11);
x_446 = l_Lean_Name_mkStr2(x_445, x_441);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_19);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_343);
lean_inc(x_327);
x_449 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_449, 0, x_327);
lean_ctor_set(x_449, 1, x_442);
lean_ctor_set(x_449, 2, x_444);
lean_ctor_set(x_449, 3, x_448);
x_450 = lean_mk_string_unchecked("tuple", 5, 5);
x_451 = l_Lean_Name_mkStr4(x_352, x_357, x_358, x_450);
x_452 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_327);
x_453 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_453, 0, x_327);
lean_ctor_set(x_453, 1, x_452);
lean_inc(x_338);
lean_inc(x_327);
x_454 = l_Lean_Syntax_node3(x_327, x_451, x_453, x_338, x_414);
lean_inc(x_336);
lean_inc(x_327);
x_455 = l_Lean_Syntax_node1(x_327, x_336, x_454);
lean_inc(x_327);
x_456 = l_Lean_Syntax_node2(x_327, x_421, x_449, x_455);
lean_inc(x_327);
x_457 = l_Lean_Syntax_node4(x_327, x_405, x_407, x_440, x_419, x_456);
lean_inc(x_327);
x_458 = l_Lean_Syntax_node2(x_327, x_336, x_433, x_457);
lean_inc(x_327);
x_459 = l_Lean_Syntax_node1(x_327, x_403, x_458);
lean_inc(x_327);
x_460 = l_Lean_Syntax_node2(x_327, x_400, x_401, x_459);
x_461 = l_Lean_Syntax_node8(x_327, x_356, x_338, x_381, x_382, x_388, x_348, x_396, x_398, x_460);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
if (lean_is_scalar(x_324)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_324;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_323);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_322);
lean_dec(x_317);
lean_free_object(x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_464 = lean_box(0);
if (lean_is_scalar(x_324)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_324;
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_323);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_317);
lean_free_object(x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_466 = lean_ctor_get(x_321, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_321, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_468 = x_321;
} else {
 lean_dec_ref(x_321);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
}
else
{
lean_object* x_470; 
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_470 = lean_ctor_get(x_15, 1);
lean_inc(x_470);
lean_dec(x_15);
x_6 = x_470;
goto block_9;
}
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_16, 1);
lean_inc(x_471);
lean_dec(x_16);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; size_t x_475; lean_object* x_476; size_t x_477; lean_object* x_478; 
x_472 = lean_ctor_get(x_15, 1);
lean_inc(x_472);
lean_dec(x_15);
x_473 = lean_ctor_get(x_18, 0);
lean_inc(x_473);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_474 = x_18;
} else {
 lean_dec_ref(x_18);
 x_474 = lean_box(0);
}
x_475 = lean_array_size(x_11);
x_476 = lean_unsigned_to_nat(0u);
x_477 = lean_usize_of_nat(x_476);
lean_inc(x_12);
x_478 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_475, x_477, x_11, x_12, x_472);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
x_482 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_479);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_483 = lean_ctor_get(x_12, 5);
lean_inc(x_483);
x_484 = l_Lean_SourceInfo_fromRef(x_483, x_482);
lean_dec(x_483);
x_485 = lean_ctor_get(x_12, 2);
lean_inc(x_485);
x_486 = lean_ctor_get(x_12, 1);
lean_inc(x_486);
lean_dec(x_12);
x_487 = lean_mk_string_unchecked("ident", 5, 5);
x_488 = lean_mk_string_unchecked("antiquot", 8, 8);
lean_inc(x_487);
x_489 = l_Lean_Name_mkStr2(x_487, x_488);
x_490 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_484);
if (lean_is_scalar(x_474)) {
 x_491 = lean_alloc_ctor(2, 2, 0);
} else {
 x_491 = x_474;
 lean_ctor_set_tag(x_491, 2);
}
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_mk_string_unchecked("null", 4, 4);
x_493 = l_Lean_Name_mkStr1(x_492);
x_494 = l_Array_mkArray0(lean_box(0));
lean_inc(x_493);
lean_inc(x_484);
x_495 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_495, 0, x_484);
lean_ctor_set(x_495, 1, x_493);
lean_ctor_set(x_495, 2, x_494);
x_496 = lean_mk_string_unchecked("f", 1, 1);
lean_inc(x_496);
x_497 = l_String_toSubstring_x27(x_496);
x_498 = l_Lean_Name_mkStr1(x_496);
lean_inc(x_485);
lean_inc(x_486);
x_499 = l_Lean_addMacroScope(x_486, x_498, x_485);
x_500 = lean_box(0);
lean_inc(x_484);
x_501 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_501, 0, x_484);
lean_ctor_set(x_501, 1, x_497);
lean_ctor_set(x_501, 2, x_499);
lean_ctor_set(x_501, 3, x_500);
x_502 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_503 = l_Lean_Name_mkStr1(x_502);
x_504 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_484);
x_505 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_505, 0, x_484);
lean_ctor_set(x_505, 1, x_504);
lean_inc(x_484);
x_506 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_506, 0, x_484);
lean_ctor_set(x_506, 1, x_487);
lean_inc(x_505);
lean_inc(x_484);
x_507 = l_Lean_Syntax_node2(x_484, x_503, x_505, x_506);
lean_inc(x_501);
lean_inc(x_495);
lean_inc(x_484);
x_508 = l_Lean_Syntax_node4(x_484, x_489, x_491, x_495, x_501, x_507);
x_509 = lean_mk_string_unchecked("Lean", 4, 4);
x_510 = lean_mk_string_unchecked("Elab", 4, 4);
x_511 = lean_mk_string_unchecked("Command", 7, 7);
x_512 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_512);
lean_inc(x_509);
x_513 = l_Lean_Name_mkStr4(x_509, x_510, x_511, x_512);
x_514 = lean_mk_string_unchecked("Parser", 6, 6);
x_515 = lean_mk_string_unchecked("Term", 4, 4);
x_516 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_517 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_516);
x_518 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_484);
x_519 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_519, 0, x_484);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_521 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_520);
x_522 = lean_mk_string_unchecked("Attr", 4, 4);
x_523 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_514);
lean_inc(x_509);
x_524 = l_Lean_Name_mkStr4(x_509, x_514, x_522, x_523);
x_525 = lean_mk_string_unchecked("app_unexpander", 14, 14);
lean_inc(x_525);
x_526 = l_String_toSubstring_x27(x_525);
x_527 = l_Lean_Name_mkStr1(x_525);
lean_inc(x_485);
lean_inc(x_486);
x_528 = l_Lean_addMacroScope(x_486, x_527, x_485);
lean_inc(x_484);
x_529 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_529, 0, x_484);
lean_ctor_set(x_529, 1, x_526);
lean_ctor_set(x_529, 2, x_528);
lean_ctor_set(x_529, 3, x_500);
x_530 = lean_mk_syntax_ident(x_473);
lean_inc(x_530);
lean_inc(x_493);
lean_inc(x_484);
x_531 = l_Lean_Syntax_node1(x_484, x_493, x_530);
lean_inc(x_484);
x_532 = l_Lean_Syntax_node2(x_484, x_524, x_529, x_531);
lean_inc(x_484);
x_533 = l_Lean_Syntax_node2(x_484, x_521, x_1, x_532);
lean_inc(x_493);
lean_inc(x_484);
x_534 = l_Lean_Syntax_node1(x_484, x_493, x_533);
x_535 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_484);
x_536 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_536, 0, x_484);
lean_ctor_set(x_536, 1, x_535);
lean_inc(x_484);
x_537 = l_Lean_Syntax_node3(x_484, x_517, x_519, x_534, x_536);
lean_inc(x_493);
lean_inc(x_484);
x_538 = l_Lean_Syntax_node1(x_484, x_493, x_537);
lean_inc(x_484);
x_539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_539, 0, x_484);
lean_ctor_set(x_539, 1, x_512);
x_540 = lean_mk_string_unchecked("unexpand", 8, 8);
lean_inc(x_540);
x_541 = l_String_toSubstring_x27(x_540);
x_542 = l_Lean_Name_mkStr1(x_540);
lean_inc(x_485);
lean_inc(x_486);
x_543 = l_Lean_addMacroScope(x_486, x_542, x_485);
lean_inc(x_484);
x_544 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_544, 0, x_484);
lean_ctor_set(x_544, 1, x_541);
lean_ctor_set(x_544, 2, x_543);
lean_ctor_set(x_544, 3, x_500);
lean_inc(x_493);
lean_inc(x_484);
x_545 = l_Lean_Syntax_node2(x_484, x_493, x_544, x_530);
x_546 = lean_mk_string_unchecked("Lean.PrettyPrinter.Unexpander", 29, 29);
x_547 = l_String_toSubstring_x27(x_546);
x_548 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_549 = lean_mk_string_unchecked("Unexpander", 10, 10);
lean_inc(x_509);
x_550 = l_Lean_Name_mkStr3(x_509, x_548, x_549);
lean_inc(x_485);
lean_inc(x_550);
lean_inc(x_486);
x_551 = l_Lean_addMacroScope(x_486, x_550, x_485);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_19);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_500);
lean_inc(x_484);
x_554 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_554, 0, x_484);
lean_ctor_set(x_554, 1, x_547);
lean_ctor_set(x_554, 2, x_551);
lean_ctor_set(x_554, 3, x_553);
x_555 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_484);
x_556 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_556, 0, x_484);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_557);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_558 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_557);
lean_inc(x_484);
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_484);
lean_ctor_set(x_559, 1, x_557);
x_560 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_561 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_560);
x_562 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_563 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_562);
x_564 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_484);
x_565 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_565, 0, x_484);
lean_ctor_set(x_565, 1, x_564);
x_566 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_567 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_566);
x_568 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_484);
x_569 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_569, 0, x_484);
lean_ctor_set(x_569, 1, x_568);
x_570 = l_Lean_Syntax_mkApp(x_508, x_479);
x_571 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_484);
x_572 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_572, 0, x_484);
lean_ctor_set(x_572, 1, x_571);
lean_inc(x_572);
lean_inc(x_569);
lean_inc(x_567);
lean_inc(x_484);
x_573 = l_Lean_Syntax_node3(x_484, x_567, x_569, x_570, x_572);
lean_inc(x_493);
lean_inc(x_484);
x_574 = l_Lean_Syntax_node1(x_484, x_493, x_573);
lean_inc(x_493);
lean_inc(x_484);
x_575 = l_Lean_Syntax_node1(x_484, x_493, x_574);
x_576 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_484);
x_577 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_577, 0, x_484);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_579 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_578);
x_580 = lean_mk_string_unchecked("withRef", 7, 7);
lean_inc(x_580);
x_581 = l_String_toSubstring_x27(x_580);
lean_inc(x_580);
x_582 = l_Lean_Name_mkStr1(x_580);
lean_inc(x_485);
lean_inc(x_486);
x_583 = l_Lean_addMacroScope(x_486, x_582, x_485);
lean_inc(x_509);
x_584 = l_Lean_Name_mkStr2(x_509, x_580);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_19);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_500);
lean_inc(x_484);
x_587 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_587, 0, x_484);
lean_ctor_set(x_587, 1, x_581);
lean_ctor_set(x_587, 2, x_583);
lean_ctor_set(x_587, 3, x_586);
lean_inc(x_572);
lean_inc(x_484);
x_588 = l_Lean_Syntax_node3(x_484, x_567, x_569, x_2, x_572);
lean_inc(x_493);
lean_inc(x_484);
x_589 = l_Lean_Syntax_node2(x_484, x_493, x_501, x_588);
lean_inc(x_579);
lean_inc(x_484);
x_590 = l_Lean_Syntax_node2(x_484, x_579, x_587, x_589);
lean_inc(x_577);
lean_inc(x_565);
lean_inc(x_563);
lean_inc(x_484);
x_591 = l_Lean_Syntax_node4(x_484, x_563, x_565, x_575, x_577, x_590);
x_592 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_509);
x_593 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_592);
x_594 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_484);
x_595 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_595, 0, x_484);
lean_ctor_set(x_595, 1, x_594);
lean_inc(x_484);
x_596 = l_Lean_Syntax_node1(x_484, x_593, x_595);
lean_inc(x_493);
lean_inc(x_484);
x_597 = l_Lean_Syntax_node1(x_484, x_493, x_596);
lean_inc(x_493);
lean_inc(x_484);
x_598 = l_Lean_Syntax_node1(x_484, x_493, x_597);
x_599 = lean_mk_string_unchecked("throw", 5, 5);
lean_inc(x_599);
x_600 = l_String_toSubstring_x27(x_599);
lean_inc(x_599);
x_601 = l_Lean_Name_mkStr1(x_599);
x_602 = l_Lean_addMacroScope(x_486, x_601, x_485);
x_603 = lean_mk_string_unchecked("MonadExcept", 11, 11);
x_604 = l_Lean_Name_mkStr2(x_603, x_599);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_19);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_500);
lean_inc(x_484);
x_607 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_607, 0, x_484);
lean_ctor_set(x_607, 1, x_600);
lean_ctor_set(x_607, 2, x_602);
lean_ctor_set(x_607, 3, x_606);
x_608 = lean_mk_string_unchecked("tuple", 5, 5);
x_609 = l_Lean_Name_mkStr4(x_509, x_514, x_515, x_608);
x_610 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_484);
x_611 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_611, 0, x_484);
lean_ctor_set(x_611, 1, x_610);
lean_inc(x_495);
lean_inc(x_484);
x_612 = l_Lean_Syntax_node3(x_484, x_609, x_611, x_495, x_572);
lean_inc(x_493);
lean_inc(x_484);
x_613 = l_Lean_Syntax_node1(x_484, x_493, x_612);
lean_inc(x_484);
x_614 = l_Lean_Syntax_node2(x_484, x_579, x_607, x_613);
lean_inc(x_484);
x_615 = l_Lean_Syntax_node4(x_484, x_563, x_565, x_598, x_577, x_614);
lean_inc(x_484);
x_616 = l_Lean_Syntax_node2(x_484, x_493, x_591, x_615);
lean_inc(x_484);
x_617 = l_Lean_Syntax_node1(x_484, x_561, x_616);
lean_inc(x_484);
x_618 = l_Lean_Syntax_node2(x_484, x_558, x_559, x_617);
x_619 = l_Lean_Syntax_node8(x_484, x_513, x_495, x_538, x_539, x_545, x_505, x_554, x_556, x_618);
x_620 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_620, 0, x_619);
if (lean_is_scalar(x_481)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_481;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_480);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; 
lean_dec(x_479);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_622 = lean_box(0);
if (lean_is_scalar(x_481)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_481;
}
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_480);
return x_623;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_624 = lean_ctor_get(x_478, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_478, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_626 = x_478;
} else {
 lean_dec_ref(x_478);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
else
{
lean_object* x_628; 
lean_dec(x_471);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_628 = lean_ctor_get(x_15, 1);
lean_inc(x_628);
lean_dec(x_15);
x_6 = x_628;
goto block_9;
}
}
}
else
{
lean_object* x_629; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_629 = lean_ctor_get(x_15, 1);
lean_inc(x_629);
lean_dec(x_15);
x_6 = x_629;
goto block_9;
}
}
}
else
{
uint8_t x_630; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_630 = !lean_is_exclusive(x_15);
if (x_630 == 0)
{
return x_15;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_15, 0);
x_632 = lean_ctor_get(x_15, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_15);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_9 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_9 = l_Lean_Syntax_getArg(x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_Elab_Command_expandNotationItemIntoPattern(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_12);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Command", 7, 7);
x_17 = lean_mk_string_unchecked("identPrec", 9, 9);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_name_eq(x_13, x_18);
lean_dec(x_18);
lean_dec(x_13);
if (x_19 == 0)
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_20; 
x_20 = lean_array_push(x_4, x_12);
x_5 = x_20;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_12; 
x_12 = l_Lean_Elab_Command_isLocalAttrKind(x_2);
if (x_12 == 0)
{
x_5 = x_12;
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_Name_hasMacroScopes(x_1);
if (x_13 == 0)
{
x_5 = x_12;
goto block_11;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
block_11:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_addMacroScope(x_7, x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_60; 
x_60 = l_Lean_evalOptPrio(x_8, x_11, x_12);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_size(x_9);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
lean_inc(x_11);
lean_inc(x_9);
x_66 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(x_63, x_65, x_9, x_11, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_mk_string_unchecked("term", 4, 4);
x_70 = l_Lean_Name_mkStr1(x_69);
x_71 = lean_box(0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_536 = lean_mk_string_unchecked("null", 4, 4);
x_537 = l_Lean_Name_mkStr1(x_536);
x_538 = lean_box(2);
lean_inc(x_67);
x_539 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_537);
lean_ctor_set(x_539, 2, x_67);
lean_inc(x_11);
lean_inc(x_70);
x_540 = l_Lean_Elab_Command_mkNameFromParserSyntax(x_70, x_539, x_11, x_68);
lean_dec(x_539);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
lean_inc(x_11);
lean_inc(x_5);
x_543 = l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(x_541, x_5, x_11, x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_526 = x_544;
x_527 = x_11;
x_528 = x_545;
goto block_535;
}
else
{
uint8_t x_546; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_546 = !lean_is_exclusive(x_540);
if (x_546 == 0)
{
return x_540;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_540, 0);
x_548 = lean_ctor_get(x_540, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_540);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
return x_549;
}
}
}
else
{
lean_object* x_550; lean_object* x_551; 
x_550 = lean_ctor_get(x_7, 0);
lean_inc(x_550);
x_551 = l_Lean_Syntax_getId(x_550);
lean_dec(x_550);
x_526 = x_551;
x_527 = x_11;
x_528 = x_68;
goto block_535;
}
block_393:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_95 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_95);
lean_inc(x_80);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_80);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_96);
lean_inc(x_93);
lean_inc(x_73);
lean_inc(x_80);
x_97 = l_Lean_Syntax_node5(x_80, x_75, x_73, x_86, x_93, x_94, x_96);
lean_inc(x_87);
lean_inc(x_80);
x_98 = l_Lean_Syntax_node1(x_80, x_87, x_97);
x_99 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_100 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_99);
x_101 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_80);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_80);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Init_Data_Repr_0__Nat_reprFast(x_61);
lean_inc(x_89);
x_104 = l_Lean_Syntax_mkNumLit(x_103, x_89);
lean_inc(x_80);
x_105 = l_Lean_Syntax_node5(x_80, x_100, x_73, x_102, x_93, x_104, x_96);
lean_inc(x_87);
lean_inc(x_80);
x_106 = l_Lean_Syntax_node1(x_80, x_87, x_105);
x_107 = lean_array_size(x_67);
x_108 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_107, x_65, x_67);
lean_inc(x_85);
x_109 = l_Array_append(lean_box(0), x_85, x_108);
lean_dec(x_108);
lean_inc(x_87);
lean_inc(x_80);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_80);
lean_ctor_set(x_110, 1, x_87);
lean_ctor_set(x_110, 2, x_109);
x_111 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_80);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_80);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_unsigned_to_nat(10u);
x_114 = lean_mk_empty_array_with_capacity(x_113);
x_115 = lean_array_push(x_114, x_83);
x_116 = lean_array_push(x_115, x_84);
lean_inc(x_5);
x_117 = lean_array_push(x_116, x_5);
x_118 = lean_array_push(x_117, x_78);
x_119 = lean_array_push(x_118, x_74);
x_120 = lean_array_push(x_119, x_98);
x_121 = lean_array_push(x_120, x_106);
x_122 = lean_array_push(x_121, x_110);
x_123 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_72, x_72, x_81);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(x_125, x_72, x_126);
lean_dec(x_125);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
x_131 = lean_unbox(x_71);
x_132 = l_Lean_mkIdentFrom(x_1, x_70, x_131);
x_133 = lean_array_push(x_122, x_112);
x_134 = lean_array_push(x_133, x_132);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_80);
lean_ctor_set(x_135, 1, x_88);
lean_ctor_set(x_135, 2, x_134);
x_136 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_136);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_137 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_136);
lean_inc(x_85);
lean_inc(x_87);
lean_inc(x_129);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_129);
lean_ctor_set(x_138, 1, x_87);
lean_ctor_set(x_138, 2, x_85);
x_139 = lean_mk_string_unchecked("Term", 4, 4);
x_140 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_139);
lean_inc(x_91);
lean_inc(x_90);
x_141 = l_Lean_Name_mkStr4(x_90, x_91, x_139, x_140);
lean_inc(x_138);
lean_inc(x_129);
x_142 = l_Lean_Syntax_node1(x_129, x_141, x_138);
lean_inc(x_129);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_136);
x_143 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_139);
lean_inc(x_91);
lean_inc(x_90);
x_144 = l_Lean_Name_mkStr4(x_90, x_91, x_139, x_143);
x_145 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_139);
lean_inc(x_91);
lean_inc(x_90);
x_146 = l_Lean_Name_mkStr4(x_90, x_91, x_139, x_145);
x_147 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_129);
lean_ctor_set_tag(x_123, 2);
lean_ctor_set(x_123, 1, x_147);
lean_ctor_set(x_123, 0, x_129);
x_148 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_139);
lean_inc(x_91);
lean_inc(x_90);
x_149 = l_Lean_Name_mkStr4(x_90, x_91, x_139, x_148);
x_150 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_129);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_129);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_129);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_129);
lean_ctor_set(x_152, 1, x_95);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_149);
lean_inc(x_129);
x_153 = l_Lean_Syntax_node3(x_129, x_149, x_151, x_77, x_152);
lean_inc(x_87);
lean_inc(x_129);
x_154 = l_Lean_Syntax_node1(x_129, x_87, x_153);
lean_inc(x_87);
lean_inc(x_129);
x_155 = l_Lean_Syntax_node1(x_129, x_87, x_154);
x_156 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_129);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_129);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_mk_string_unchecked("precheckedQuot", 14, 14);
lean_inc(x_91);
lean_inc(x_90);
x_159 = l_Lean_Name_mkStr4(x_90, x_91, x_139, x_158);
x_160 = lean_mk_string_unchecked("`", 1, 1);
lean_inc(x_129);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_129);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_129);
x_162 = l_Lean_Syntax_node3(x_129, x_149, x_151, x_82, x_152);
lean_inc(x_129);
x_163 = l_Lean_Syntax_node2(x_129, x_159, x_161, x_162);
lean_inc(x_129);
x_164 = l_Lean_Syntax_node4(x_129, x_146, x_123, x_155, x_157, x_163);
lean_inc(x_87);
lean_inc(x_129);
x_165 = l_Lean_Syntax_node1(x_129, x_87, x_164);
lean_inc(x_129);
x_166 = l_Lean_Syntax_node1(x_129, x_144, x_165);
lean_inc_n(x_138, 2);
x_167 = l_Lean_Syntax_node6(x_129, x_137, x_138, x_138, x_142, x_127, x_138, x_166);
lean_inc(x_5);
x_168 = l_Lean_Elab_Command_isLocalAttrKind(x_5);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_85);
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_mk_empty_array_with_capacity(x_169);
x_171 = lean_array_push(x_170, x_167);
lean_inc(x_87);
lean_inc(x_89);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_89);
lean_ctor_set(x_172, 1, x_87);
lean_ctor_set(x_172, 2, x_171);
x_13 = x_87;
x_14 = x_135;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_172;
x_19 = x_72;
x_20 = x_130;
goto block_59;
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_72, x_72, x_130);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
x_177 = lean_unbox(x_71);
x_178 = l_Lean_SourceInfo_fromRef(x_175, x_177);
lean_dec(x_175);
x_179 = lean_ctor_get(x_72, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_72, 1);
lean_inc(x_180);
x_181 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_181);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_182 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_181);
lean_inc(x_178);
lean_ctor_set_tag(x_173, 2);
lean_ctor_set(x_173, 1, x_181);
lean_ctor_set(x_173, 0, x_178);
lean_inc(x_87);
lean_inc(x_178);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_87);
lean_ctor_set(x_183, 2, x_85);
lean_inc(x_183);
lean_inc(x_178);
x_184 = l_Lean_Syntax_node2(x_178, x_182, x_173, x_183);
x_185 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_185);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_186 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_185);
lean_inc(x_178);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_185);
x_188 = lean_mk_string_unchecked("quotPrecheck.allowSectionVars", 29, 29);
x_189 = l_String_toSubstring_x27(x_188);
x_190 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
x_191 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
x_192 = l_Lean_Name_mkStr2(x_190, x_191);
x_193 = l_Lean_addMacroScope(x_180, x_192, x_179);
x_194 = lean_box(0);
lean_inc(x_178);
x_195 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_195, 0, x_178);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_178);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_178);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_183);
lean_inc(x_178);
x_198 = l_Lean_Syntax_node4(x_178, x_186, x_187, x_195, x_183, x_197);
x_199 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_199);
x_200 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_199);
lean_inc(x_178);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_178);
lean_ctor_set(x_201, 1, x_199);
lean_inc(x_178);
x_202 = l_Lean_Syntax_node2(x_178, x_200, x_201, x_183);
lean_inc(x_87);
x_203 = l_Lean_Syntax_node4(x_178, x_87, x_184, x_198, x_167, x_202);
x_13 = x_87;
x_14 = x_135;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_203;
x_19 = x_72;
x_20 = x_176;
goto block_59;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_204 = lean_ctor_get(x_173, 0);
x_205 = lean_ctor_get(x_173, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_173);
x_206 = lean_unbox(x_71);
x_207 = l_Lean_SourceInfo_fromRef(x_204, x_206);
lean_dec(x_204);
x_208 = lean_ctor_get(x_72, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_72, 1);
lean_inc(x_209);
x_210 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_210);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_211 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_210);
lean_inc(x_207);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_210);
lean_inc(x_87);
lean_inc(x_207);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_87);
lean_ctor_set(x_213, 2, x_85);
lean_inc(x_213);
lean_inc(x_207);
x_214 = l_Lean_Syntax_node2(x_207, x_211, x_212, x_213);
x_215 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_215);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_216 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_215);
lean_inc(x_207);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_mk_string_unchecked("quotPrecheck.allowSectionVars", 29, 29);
x_219 = l_String_toSubstring_x27(x_218);
x_220 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
x_221 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
x_222 = l_Lean_Name_mkStr2(x_220, x_221);
x_223 = l_Lean_addMacroScope(x_209, x_222, x_208);
x_224 = lean_box(0);
lean_inc(x_207);
x_225 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_225, 0, x_207);
lean_ctor_set(x_225, 1, x_219);
lean_ctor_set(x_225, 2, x_223);
lean_ctor_set(x_225, 3, x_224);
x_226 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_207);
x_227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_227, 0, x_207);
lean_ctor_set(x_227, 1, x_226);
lean_inc(x_213);
lean_inc(x_207);
x_228 = l_Lean_Syntax_node4(x_207, x_216, x_217, x_225, x_213, x_227);
x_229 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_229);
x_230 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_229);
lean_inc(x_207);
x_231 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_231, 0, x_207);
lean_ctor_set(x_231, 1, x_229);
lean_inc(x_207);
x_232 = l_Lean_Syntax_node2(x_207, x_230, x_231, x_213);
lean_inc(x_87);
x_233 = l_Lean_Syntax_node4(x_207, x_87, x_214, x_228, x_167, x_232);
x_13 = x_87;
x_14 = x_135;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_233;
x_19 = x_72;
x_20 = x_205;
goto block_59;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_234 = lean_ctor_get(x_127, 0);
x_235 = lean_ctor_get(x_127, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_127);
x_236 = lean_unbox(x_71);
x_237 = l_Lean_mkIdentFrom(x_1, x_70, x_236);
x_238 = lean_array_push(x_122, x_112);
x_239 = lean_array_push(x_238, x_237);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_80);
lean_ctor_set(x_240, 1, x_88);
lean_ctor_set(x_240, 2, x_239);
x_241 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_241);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_242 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_241);
lean_inc(x_85);
lean_inc(x_87);
lean_inc(x_234);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_87);
lean_ctor_set(x_243, 2, x_85);
x_244 = lean_mk_string_unchecked("Term", 4, 4);
x_245 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_244);
lean_inc(x_91);
lean_inc(x_90);
x_246 = l_Lean_Name_mkStr4(x_90, x_91, x_244, x_245);
lean_inc(x_243);
lean_inc(x_234);
x_247 = l_Lean_Syntax_node1(x_234, x_246, x_243);
lean_inc(x_234);
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_234);
lean_ctor_set(x_248, 1, x_241);
x_249 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_244);
lean_inc(x_91);
lean_inc(x_90);
x_250 = l_Lean_Name_mkStr4(x_90, x_91, x_244, x_249);
x_251 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_244);
lean_inc(x_91);
lean_inc(x_90);
x_252 = l_Lean_Name_mkStr4(x_90, x_91, x_244, x_251);
x_253 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_234);
lean_ctor_set_tag(x_123, 2);
lean_ctor_set(x_123, 1, x_253);
lean_ctor_set(x_123, 0, x_234);
x_254 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_244);
lean_inc(x_91);
lean_inc(x_90);
x_255 = l_Lean_Name_mkStr4(x_90, x_91, x_244, x_254);
x_256 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_234);
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_234);
lean_ctor_set(x_257, 1, x_256);
lean_inc(x_234);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_234);
lean_ctor_set(x_258, 1, x_95);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_255);
lean_inc(x_234);
x_259 = l_Lean_Syntax_node3(x_234, x_255, x_257, x_77, x_258);
lean_inc(x_87);
lean_inc(x_234);
x_260 = l_Lean_Syntax_node1(x_234, x_87, x_259);
lean_inc(x_87);
lean_inc(x_234);
x_261 = l_Lean_Syntax_node1(x_234, x_87, x_260);
x_262 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_234);
x_263 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_263, 0, x_234);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_mk_string_unchecked("precheckedQuot", 14, 14);
lean_inc(x_91);
lean_inc(x_90);
x_265 = l_Lean_Name_mkStr4(x_90, x_91, x_244, x_264);
x_266 = lean_mk_string_unchecked("`", 1, 1);
lean_inc(x_234);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_234);
lean_ctor_set(x_267, 1, x_266);
lean_inc(x_234);
x_268 = l_Lean_Syntax_node3(x_234, x_255, x_257, x_82, x_258);
lean_inc(x_234);
x_269 = l_Lean_Syntax_node2(x_234, x_265, x_267, x_268);
lean_inc(x_234);
x_270 = l_Lean_Syntax_node4(x_234, x_252, x_123, x_261, x_263, x_269);
lean_inc(x_87);
lean_inc(x_234);
x_271 = l_Lean_Syntax_node1(x_234, x_87, x_270);
lean_inc(x_234);
x_272 = l_Lean_Syntax_node1(x_234, x_250, x_271);
lean_inc_n(x_243, 2);
x_273 = l_Lean_Syntax_node6(x_234, x_242, x_243, x_243, x_247, x_248, x_243, x_272);
lean_inc(x_5);
x_274 = l_Lean_Elab_Command_isLocalAttrKind(x_5);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_85);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_mk_empty_array_with_capacity(x_275);
x_277 = lean_array_push(x_276, x_273);
lean_inc(x_87);
lean_inc(x_89);
x_278 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_278, 0, x_89);
lean_ctor_set(x_278, 1, x_87);
lean_ctor_set(x_278, 2, x_277);
x_13 = x_87;
x_14 = x_240;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_278;
x_19 = x_72;
x_20 = x_235;
goto block_59;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_279 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_72, x_72, x_235);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_282 = x_279;
} else {
 lean_dec_ref(x_279);
 x_282 = lean_box(0);
}
x_283 = lean_unbox(x_71);
x_284 = l_Lean_SourceInfo_fromRef(x_280, x_283);
lean_dec(x_280);
x_285 = lean_ctor_get(x_72, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_72, 1);
lean_inc(x_286);
x_287 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_287);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_288 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_287);
lean_inc(x_284);
if (lean_is_scalar(x_282)) {
 x_289 = lean_alloc_ctor(2, 2, 0);
} else {
 x_289 = x_282;
 lean_ctor_set_tag(x_289, 2);
}
lean_ctor_set(x_289, 0, x_284);
lean_ctor_set(x_289, 1, x_287);
lean_inc(x_87);
lean_inc(x_284);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_87);
lean_ctor_set(x_290, 2, x_85);
lean_inc(x_290);
lean_inc(x_284);
x_291 = l_Lean_Syntax_node2(x_284, x_288, x_289, x_290);
x_292 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_292);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_293 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_292);
lean_inc(x_284);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_284);
lean_ctor_set(x_294, 1, x_292);
x_295 = lean_mk_string_unchecked("quotPrecheck.allowSectionVars", 29, 29);
x_296 = l_String_toSubstring_x27(x_295);
x_297 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
x_298 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
x_299 = l_Lean_Name_mkStr2(x_297, x_298);
x_300 = l_Lean_addMacroScope(x_286, x_299, x_285);
x_301 = lean_box(0);
lean_inc(x_284);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_284);
lean_ctor_set(x_302, 1, x_296);
lean_ctor_set(x_302, 2, x_300);
lean_ctor_set(x_302, 3, x_301);
x_303 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_284);
x_304 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_304, 0, x_284);
lean_ctor_set(x_304, 1, x_303);
lean_inc(x_290);
lean_inc(x_284);
x_305 = l_Lean_Syntax_node4(x_284, x_293, x_294, x_302, x_290, x_304);
x_306 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_306);
x_307 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_306);
lean_inc(x_284);
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_284);
lean_ctor_set(x_308, 1, x_306);
lean_inc(x_284);
x_309 = l_Lean_Syntax_node2(x_284, x_307, x_308, x_290);
lean_inc(x_87);
x_310 = l_Lean_Syntax_node4(x_284, x_87, x_291, x_305, x_273, x_309);
x_13 = x_87;
x_14 = x_240;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_310;
x_19 = x_72;
x_20 = x_281;
goto block_59;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_311 = lean_ctor_get(x_123, 0);
x_312 = lean_ctor_get(x_123, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_123);
x_313 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(x_311, x_72, x_312);
lean_dec(x_311);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_316 = x_313;
} else {
 lean_dec_ref(x_313);
 x_316 = lean_box(0);
}
x_317 = lean_unbox(x_71);
x_318 = l_Lean_mkIdentFrom(x_1, x_70, x_317);
x_319 = lean_array_push(x_122, x_112);
x_320 = lean_array_push(x_319, x_318);
x_321 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_321, 0, x_80);
lean_ctor_set(x_321, 1, x_88);
lean_ctor_set(x_321, 2, x_320);
x_322 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_322);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_323 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_322);
lean_inc(x_85);
lean_inc(x_87);
lean_inc(x_314);
x_324 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_87);
lean_ctor_set(x_324, 2, x_85);
x_325 = lean_mk_string_unchecked("Term", 4, 4);
x_326 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_325);
lean_inc(x_91);
lean_inc(x_90);
x_327 = l_Lean_Name_mkStr4(x_90, x_91, x_325, x_326);
lean_inc(x_324);
lean_inc(x_314);
x_328 = l_Lean_Syntax_node1(x_314, x_327, x_324);
lean_inc(x_314);
if (lean_is_scalar(x_316)) {
 x_329 = lean_alloc_ctor(2, 2, 0);
} else {
 x_329 = x_316;
 lean_ctor_set_tag(x_329, 2);
}
lean_ctor_set(x_329, 0, x_314);
lean_ctor_set(x_329, 1, x_322);
x_330 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_325);
lean_inc(x_91);
lean_inc(x_90);
x_331 = l_Lean_Name_mkStr4(x_90, x_91, x_325, x_330);
x_332 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_325);
lean_inc(x_91);
lean_inc(x_90);
x_333 = l_Lean_Name_mkStr4(x_90, x_91, x_325, x_332);
x_334 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_314);
x_335 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_335, 0, x_314);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_325);
lean_inc(x_91);
lean_inc(x_90);
x_337 = l_Lean_Name_mkStr4(x_90, x_91, x_325, x_336);
x_338 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_314);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_314);
lean_ctor_set(x_339, 1, x_338);
lean_inc(x_314);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_314);
lean_ctor_set(x_340, 1, x_95);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_337);
lean_inc(x_314);
x_341 = l_Lean_Syntax_node3(x_314, x_337, x_339, x_77, x_340);
lean_inc(x_87);
lean_inc(x_314);
x_342 = l_Lean_Syntax_node1(x_314, x_87, x_341);
lean_inc(x_87);
lean_inc(x_314);
x_343 = l_Lean_Syntax_node1(x_314, x_87, x_342);
x_344 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_314);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_314);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_mk_string_unchecked("precheckedQuot", 14, 14);
lean_inc(x_91);
lean_inc(x_90);
x_347 = l_Lean_Name_mkStr4(x_90, x_91, x_325, x_346);
x_348 = lean_mk_string_unchecked("`", 1, 1);
lean_inc(x_314);
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_314);
lean_ctor_set(x_349, 1, x_348);
lean_inc(x_314);
x_350 = l_Lean_Syntax_node3(x_314, x_337, x_339, x_82, x_340);
lean_inc(x_314);
x_351 = l_Lean_Syntax_node2(x_314, x_347, x_349, x_350);
lean_inc(x_314);
x_352 = l_Lean_Syntax_node4(x_314, x_333, x_335, x_343, x_345, x_351);
lean_inc(x_87);
lean_inc(x_314);
x_353 = l_Lean_Syntax_node1(x_314, x_87, x_352);
lean_inc(x_314);
x_354 = l_Lean_Syntax_node1(x_314, x_331, x_353);
lean_inc_n(x_324, 2);
x_355 = l_Lean_Syntax_node6(x_314, x_323, x_324, x_324, x_328, x_329, x_324, x_354);
lean_inc(x_5);
x_356 = l_Lean_Elab_Command_isLocalAttrKind(x_5);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_85);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
x_359 = lean_array_push(x_358, x_355);
lean_inc(x_87);
lean_inc(x_89);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_89);
lean_ctor_set(x_360, 1, x_87);
lean_ctor_set(x_360, 2, x_359);
x_13 = x_87;
x_14 = x_321;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_360;
x_19 = x_72;
x_20 = x_315;
goto block_59;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_361 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_72, x_72, x_315);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_364 = x_361;
} else {
 lean_dec_ref(x_361);
 x_364 = lean_box(0);
}
x_365 = lean_unbox(x_71);
x_366 = l_Lean_SourceInfo_fromRef(x_362, x_365);
lean_dec(x_362);
x_367 = lean_ctor_get(x_72, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_72, 1);
lean_inc(x_368);
x_369 = lean_mk_string_unchecked("section", 7, 7);
lean_inc(x_369);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_370 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_369);
lean_inc(x_366);
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(2, 2, 0);
} else {
 x_371 = x_364;
 lean_ctor_set_tag(x_371, 2);
}
lean_ctor_set(x_371, 0, x_366);
lean_ctor_set(x_371, 1, x_369);
lean_inc(x_87);
lean_inc(x_366);
x_372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_372, 0, x_366);
lean_ctor_set(x_372, 1, x_87);
lean_ctor_set(x_372, 2, x_85);
lean_inc(x_372);
lean_inc(x_366);
x_373 = l_Lean_Syntax_node2(x_366, x_370, x_371, x_372);
x_374 = lean_mk_string_unchecked("set_option", 10, 10);
lean_inc(x_374);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_375 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_374);
lean_inc(x_366);
x_376 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_374);
x_377 = lean_mk_string_unchecked("quotPrecheck.allowSectionVars", 29, 29);
x_378 = l_String_toSubstring_x27(x_377);
x_379 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
x_380 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
x_381 = l_Lean_Name_mkStr2(x_379, x_380);
x_382 = l_Lean_addMacroScope(x_368, x_381, x_367);
x_383 = lean_box(0);
lean_inc(x_366);
x_384 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_384, 0, x_366);
lean_ctor_set(x_384, 1, x_378);
lean_ctor_set(x_384, 2, x_382);
lean_ctor_set(x_384, 3, x_383);
x_385 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_366);
x_386 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_386, 0, x_366);
lean_ctor_set(x_386, 1, x_385);
lean_inc(x_372);
lean_inc(x_366);
x_387 = l_Lean_Syntax_node4(x_366, x_375, x_376, x_384, x_372, x_386);
x_388 = lean_mk_string_unchecked("end", 3, 3);
lean_inc(x_388);
x_389 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_388);
lean_inc(x_366);
x_390 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_390, 0, x_366);
lean_ctor_set(x_390, 1, x_388);
lean_inc(x_366);
x_391 = l_Lean_Syntax_node2(x_366, x_389, x_390, x_372);
lean_inc(x_87);
x_392 = l_Lean_Syntax_node4(x_366, x_87, x_373, x_387, x_355, x_391);
x_13 = x_87;
x_14 = x_321;
x_15 = x_76;
x_16 = x_89;
x_17 = x_79;
x_18 = x_392;
x_19 = x_72;
x_20 = x_363;
goto block_59;
}
}
}
block_425:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_inc(x_404);
x_413 = l_Array_append(lean_box(0), x_404, x_412);
lean_dec(x_412);
lean_inc(x_406);
lean_inc(x_399);
x_414 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_414, 0, x_399);
lean_ctor_set(x_414, 1, x_406);
lean_ctor_set(x_414, 2, x_413);
x_415 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
x_416 = l_Lean_Name_mkStr4(x_409, x_410, x_411, x_415);
x_417 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_399);
x_418 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_418, 0, x_399);
lean_ctor_set(x_418, 1, x_417);
x_419 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_399);
x_420 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_420, 0, x_399);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_399);
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_399);
lean_ctor_set(x_422, 1, x_421);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_423; 
x_423 = lean_mk_syntax_ident(x_405);
x_72 = x_394;
x_73 = x_418;
x_74 = x_414;
x_75 = x_416;
x_76 = x_395;
x_77 = x_396;
x_78 = x_397;
x_79 = x_398;
x_80 = x_399;
x_81 = x_400;
x_82 = x_403;
x_83 = x_402;
x_84 = x_401;
x_85 = x_404;
x_86 = x_420;
x_87 = x_406;
x_88 = x_407;
x_89 = x_408;
x_90 = x_409;
x_91 = x_410;
x_92 = x_411;
x_93 = x_422;
x_94 = x_423;
goto block_393;
}
else
{
lean_object* x_424; 
lean_dec(x_405);
x_424 = lean_ctor_get(x_7, 0);
lean_inc(x_424);
lean_dec(x_7);
x_72 = x_394;
x_73 = x_418;
x_74 = x_414;
x_75 = x_416;
x_76 = x_395;
x_77 = x_396;
x_78 = x_397;
x_79 = x_398;
x_80 = x_399;
x_81 = x_400;
x_82 = x_403;
x_83 = x_402;
x_84 = x_401;
x_85 = x_404;
x_86 = x_420;
x_87 = x_406;
x_88 = x_407;
x_89 = x_408;
x_90 = x_409;
x_91 = x_410;
x_92 = x_411;
x_93 = x_422;
x_94 = x_424;
goto block_393;
}
}
block_455:
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_inc(x_435);
x_444 = l_Array_append(lean_box(0), x_435, x_443);
lean_dec(x_443);
lean_inc(x_437);
lean_inc(x_431);
x_445 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_445, 0, x_431);
lean_ctor_set(x_445, 1, x_437);
lean_ctor_set(x_445, 2, x_444);
lean_inc(x_431);
x_446 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_446, 0, x_431);
lean_ctor_set(x_446, 1, x_430);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_447; 
x_447 = l_Array_empty(lean_box(0));
x_394 = x_426;
x_395 = x_427;
x_396 = x_428;
x_397 = x_446;
x_398 = x_429;
x_399 = x_431;
x_400 = x_432;
x_401 = x_445;
x_402 = x_433;
x_403 = x_434;
x_404 = x_435;
x_405 = x_436;
x_406 = x_437;
x_407 = x_438;
x_408 = x_439;
x_409 = x_442;
x_410 = x_441;
x_411 = x_440;
x_412 = x_447;
goto block_425;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_448 = lean_ctor_get(x_6, 0);
lean_inc(x_448);
lean_dec(x_6);
x_449 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_441);
lean_inc(x_442);
x_450 = l_Lean_Name_mkStr3(x_442, x_441, x_449);
x_451 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_431);
x_452 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_452, 0, x_431);
lean_ctor_set(x_452, 1, x_451);
lean_inc(x_431);
x_453 = l_Lean_Syntax_node2(x_431, x_450, x_452, x_448);
x_454 = l_Array_mkArray1___redArg(x_453);
x_394 = x_426;
x_395 = x_427;
x_396 = x_428;
x_397 = x_446;
x_398 = x_429;
x_399 = x_431;
x_400 = x_432;
x_401 = x_445;
x_402 = x_433;
x_403 = x_434;
x_404 = x_435;
x_405 = x_436;
x_406 = x_437;
x_407 = x_438;
x_408 = x_439;
x_409 = x_442;
x_410 = x_441;
x_411 = x_440;
x_412 = x_454;
goto block_425;
}
}
block_489:
{
lean_object* x_474; lean_object* x_475; 
lean_inc(x_464);
x_474 = l_Array_append(lean_box(0), x_464, x_473);
lean_dec(x_473);
lean_inc(x_466);
lean_inc(x_461);
x_475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_475, 0, x_461);
lean_ctor_set(x_475, 1, x_466);
lean_ctor_set(x_475, 2, x_474);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_476; 
x_476 = l_Array_empty(lean_box(0));
x_426 = x_456;
x_427 = x_457;
x_428 = x_458;
x_429 = x_459;
x_430 = x_460;
x_431 = x_461;
x_432 = x_462;
x_433 = x_475;
x_434 = x_463;
x_435 = x_464;
x_436 = x_465;
x_437 = x_466;
x_438 = x_468;
x_439 = x_469;
x_440 = x_472;
x_441 = x_471;
x_442 = x_470;
x_443 = x_476;
goto block_455;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_477 = lean_ctor_get(x_467, 0);
lean_inc(x_477);
lean_dec(x_467);
x_478 = lean_mk_string_unchecked("Term", 4, 4);
x_479 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_471);
lean_inc(x_470);
x_480 = l_Lean_Name_mkStr4(x_470, x_471, x_478, x_479);
x_481 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_461);
x_482 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_482, 0, x_461);
lean_ctor_set(x_482, 1, x_481);
lean_inc(x_464);
x_483 = l_Array_append(lean_box(0), x_464, x_477);
lean_dec(x_477);
lean_inc(x_466);
lean_inc(x_461);
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_461);
lean_ctor_set(x_484, 1, x_466);
lean_ctor_set(x_484, 2, x_483);
x_485 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_461);
x_486 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_486, 0, x_461);
lean_ctor_set(x_486, 1, x_485);
lean_inc(x_461);
x_487 = l_Lean_Syntax_node3(x_461, x_480, x_482, x_484, x_486);
x_488 = l_Array_mkArray1___redArg(x_487);
x_426 = x_456;
x_427 = x_457;
x_428 = x_458;
x_429 = x_459;
x_430 = x_460;
x_431 = x_461;
x_432 = x_462;
x_433 = x_475;
x_434 = x_463;
x_435 = x_464;
x_436 = x_465;
x_437 = x_466;
x_438 = x_468;
x_439 = x_469;
x_440 = x_472;
x_441 = x_471;
x_442 = x_470;
x_443 = x_488;
goto block_455;
}
}
block_525:
{
lean_object* x_494; 
x_494 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(x_63, x_65, x_9, x_490, x_492);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; size_t x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_490, x_490, x_496);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(x_498, x_490, x_499);
lean_dec(x_498);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_array_size(x_493);
x_504 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(x_503, x_65, x_493);
x_505 = lean_mk_string_unchecked("Lean", 4, 4);
x_506 = lean_mk_string_unchecked("Parser", 6, 6);
x_507 = lean_mk_string_unchecked("Command", 7, 7);
lean_inc(x_491);
x_508 = l_Lean_Name_append(x_2, x_491);
x_509 = lean_box(2);
lean_inc(x_10);
x_510 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_504, x_10);
lean_dec(x_504);
x_511 = l_Lean_Elab_Command_addInheritDocDefault(x_10, x_4);
x_512 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_508);
lean_ctor_set(x_512, 2, x_495);
x_513 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_513);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_505);
x_514 = l_Lean_Name_mkStr4(x_505, x_506, x_507, x_513);
x_515 = lean_mk_string_unchecked("null", 4, 4);
x_516 = l_Lean_Name_mkStr1(x_515);
x_517 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_518; 
x_518 = l_Array_empty(lean_box(0));
lean_inc(x_512);
lean_inc(x_510);
x_456 = x_490;
x_457 = x_510;
x_458 = x_512;
x_459 = x_512;
x_460 = x_513;
x_461 = x_501;
x_462 = x_502;
x_463 = x_510;
x_464 = x_517;
x_465 = x_491;
x_466 = x_516;
x_467 = x_511;
x_468 = x_514;
x_469 = x_509;
x_470 = x_505;
x_471 = x_506;
x_472 = x_507;
x_473 = x_518;
goto block_489;
}
else
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_3, 0);
lean_inc(x_519);
lean_dec(x_3);
x_520 = l_Array_mkArray1___redArg(x_519);
lean_inc(x_512);
lean_inc(x_510);
x_456 = x_490;
x_457 = x_510;
x_458 = x_512;
x_459 = x_512;
x_460 = x_513;
x_461 = x_501;
x_462 = x_502;
x_463 = x_510;
x_464 = x_517;
x_465 = x_491;
x_466 = x_516;
x_467 = x_511;
x_468 = x_514;
x_469 = x_509;
x_470 = x_505;
x_471 = x_506;
x_472 = x_507;
x_473 = x_520;
goto block_489;
}
}
else
{
uint8_t x_521; 
lean_dec(x_493);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_521 = !lean_is_exclusive(x_494);
if (x_521 == 0)
{
return x_494;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_494, 0);
x_523 = lean_ctor_get(x_494, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_494);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
block_535:
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; 
x_529 = lean_array_get_size(x_9);
x_530 = lean_mk_empty_array_with_capacity(x_64);
x_531 = lean_nat_dec_lt(x_64, x_529);
if (x_531 == 0)
{
lean_dec(x_529);
x_490 = x_527;
x_491 = x_526;
x_492 = x_528;
x_493 = x_530;
goto block_525;
}
else
{
uint8_t x_532; 
x_532 = lean_nat_dec_le(x_529, x_529);
if (x_532 == 0)
{
lean_dec(x_529);
x_490 = x_527;
x_491 = x_526;
x_492 = x_528;
x_493 = x_530;
goto block_525;
}
else
{
size_t x_533; lean_object* x_534; 
x_533 = lean_usize_of_nat(x_529);
lean_dec(x_529);
x_534 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(x_9, x_65, x_533, x_530);
x_490 = x_527;
x_491 = x_526;
x_492 = x_528;
x_493 = x_534;
goto block_525;
}
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_552 = !lean_is_exclusive(x_66);
if (x_552 == 0)
{
return x_66;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_66, 0);
x_554 = lean_ctor_get(x_66, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_66);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_556 = !lean_is_exclusive(x_60);
if (x_556 == 0)
{
return x_60;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_60, 0);
x_558 = lean_ctor_get(x_60, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_60);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
block_59:
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Command_mkUnexpander(x_5, x_17, x_15, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_14);
x_28 = lean_array_push(x_27, x_18);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_array_push(x_32, x_14);
x_34 = lean_array_push(x_33, x_18);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_13);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_21, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_array_push(x_41, x_14);
x_43 = lean_array_push(x_42, x_18);
x_44 = lean_array_push(x_43, x_39);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_13);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_21, 0, x_45);
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
lean_dec(x_22);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
x_50 = lean_array_push(x_49, x_14);
x_51 = lean_array_push(x_50, x_18);
x_52 = lean_array_push(x_51, x_47);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_13);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Command", 7, 7);
x_37 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
lean_inc(x_1);
x_39 = l_Lean_Syntax_isOfKind(x_1, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_40 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_135; uint8_t x_136; 
x_41 = lean_unsigned_to_nat(0u);
x_135 = l_Lean_Syntax_getArg(x_1, x_41);
x_136 = l_Lean_Syntax_isNone(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_unsigned_to_nat(1u);
lean_inc(x_135);
x_138 = l_Lean_Syntax_matchesNull(x_135, x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_135);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_139 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = l_Lean_Syntax_getArg(x_135, x_41);
lean_dec(x_135);
x_141 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_142 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_141);
lean_inc(x_140);
x_143 = l_Lean_Syntax_isOfKind(x_140, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_140);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_144 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_116 = x_145;
x_117 = x_2;
x_118 = x_3;
goto block_134;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_135);
x_146 = lean_box(0);
x_116 = x_146;
x_117 = x_2;
x_118 = x_3;
goto block_134;
}
block_65:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(6u);
x_53 = l_Lean_Syntax_getArg(x_1, x_52);
x_54 = l_Lean_Syntax_isNone(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_inc(x_53);
x_55 = l_Lean_Syntax_matchesNull(x_53, x_47);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_56 = l_Lean_Macro_throwUnsupported(lean_box(0), x_50, x_51);
lean_dec(x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_Syntax_getArg(x_53, x_41);
lean_dec(x_53);
x_58 = lean_mk_string_unchecked("namedPrio", 9, 9);
x_59 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_58);
lean_inc(x_57);
x_60 = l_Lean_Syntax_isOfKind(x_57, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_1);
x_61 = l_Lean_Macro_throwUnsupported(lean_box(0), x_50, x_51);
lean_dec(x_50);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Syntax_getArg(x_57, x_42);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_4 = x_49;
x_5 = x_43;
x_6 = x_45;
x_7 = x_44;
x_8 = x_46;
x_9 = x_48;
x_10 = x_63;
x_11 = x_50;
x_12 = x_51;
goto block_33;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_53);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_64 = lean_box(0);
x_4 = x_49;
x_5 = x_43;
x_6 = x_45;
x_7 = x_44;
x_8 = x_46;
x_9 = x_48;
x_10 = x_64;
x_11 = x_50;
x_12 = x_51;
goto block_33;
}
}
block_88:
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_unsigned_to_nat(5u);
x_76 = l_Lean_Syntax_getArg(x_1, x_75);
x_77 = l_Lean_Syntax_isNone(x_76);
if (x_77 == 0)
{
uint8_t x_78; 
lean_inc(x_76);
x_78 = l_Lean_Syntax_matchesNull(x_76, x_71);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_79 = l_Lean_Macro_throwUnsupported(lean_box(0), x_73, x_74);
lean_dec(x_73);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = l_Lean_Syntax_getArg(x_76, x_41);
lean_dec(x_76);
x_81 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_82 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_81);
lean_inc(x_80);
x_83 = l_Lean_Syntax_isOfKind(x_80, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_84 = l_Lean_Macro_throwUnsupported(lean_box(0), x_73, x_74);
lean_dec(x_73);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lean_Syntax_getArg(x_80, x_66);
lean_dec(x_80);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_72;
x_46 = x_69;
x_47 = x_71;
x_48 = x_70;
x_49 = x_86;
x_50 = x_73;
x_51 = x_74;
goto block_65;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_76);
x_87 = lean_box(0);
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_72;
x_46 = x_69;
x_47 = x_71;
x_48 = x_70;
x_49 = x_87;
x_50 = x_73;
x_51 = x_74;
goto block_65;
}
}
block_115:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_94 = lean_unsigned_to_nat(2u);
x_95 = l_Lean_Syntax_getArg(x_1, x_94);
x_96 = lean_mk_string_unchecked("Term", 4, 4);
x_97 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_35);
lean_inc(x_34);
x_98 = l_Lean_Name_mkStr4(x_34, x_35, x_96, x_97);
lean_inc(x_95);
x_99 = l_Lean_Syntax_isOfKind(x_95, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_100 = l_Lean_Macro_throwUnsupported(lean_box(0), x_92, x_93);
lean_dec(x_92);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_unsigned_to_nat(4u);
x_103 = l_Lean_Syntax_getArg(x_1, x_102);
x_104 = l_Lean_Syntax_isNone(x_103);
if (x_104 == 0)
{
uint8_t x_105; 
lean_inc(x_103);
x_105 = l_Lean_Syntax_matchesNull(x_103, x_89);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_106 = l_Lean_Macro_throwUnsupported(lean_box(0), x_92, x_93);
lean_dec(x_92);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = l_Lean_Syntax_getArg(x_103, x_41);
lean_dec(x_103);
x_108 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
x_109 = l_Lean_Name_mkStr3(x_34, x_35, x_108);
lean_inc(x_107);
x_110 = l_Lean_Syntax_isOfKind(x_107, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_107);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_111 = l_Lean_Macro_throwUnsupported(lean_box(0), x_92, x_93);
lean_dec(x_92);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lean_Syntax_getArg(x_107, x_89);
lean_dec(x_107);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_66 = x_101;
x_67 = x_95;
x_68 = x_91;
x_69 = x_94;
x_70 = x_90;
x_71 = x_89;
x_72 = x_113;
x_73 = x_92;
x_74 = x_93;
goto block_88;
}
}
}
else
{
lean_object* x_114; 
lean_dec(x_103);
x_114 = lean_box(0);
x_66 = x_101;
x_67 = x_95;
x_68 = x_91;
x_69 = x_94;
x_70 = x_90;
x_71 = x_89;
x_72 = x_114;
x_73 = x_92;
x_74 = x_93;
goto block_88;
}
}
}
block_134:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_unsigned_to_nat(1u);
x_120 = l_Lean_Syntax_getArg(x_1, x_119);
x_121 = l_Lean_Syntax_isNone(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_inc(x_120);
x_122 = l_Lean_Syntax_matchesNull(x_120, x_119);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_116);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_123 = l_Lean_Macro_throwUnsupported(lean_box(0), x_117, x_118);
lean_dec(x_117);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = l_Lean_Syntax_getArg(x_120, x_41);
lean_dec(x_120);
x_125 = lean_mk_string_unchecked("Term", 4, 4);
x_126 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
x_127 = l_Lean_Name_mkStr4(x_34, x_35, x_125, x_126);
lean_inc(x_124);
x_128 = l_Lean_Syntax_isOfKind(x_124, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_124);
lean_dec(x_116);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_129 = l_Lean_Macro_throwUnsupported(lean_box(0), x_117, x_118);
lean_dec(x_117);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = l_Lean_Syntax_getArg(x_124, x_119);
lean_dec(x_124);
x_131 = l_Lean_Syntax_getArgs(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_89 = x_119;
x_90 = x_116;
x_91 = x_132;
x_92 = x_117;
x_93 = x_118;
goto block_115;
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_120);
x_133 = lean_box(0);
x_89 = x_119;
x_90 = x_116;
x_91 = x_133;
x_92 = x_117;
x_93 = x_118;
goto block_115;
}
}
}
block_33:
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = l_Lean_Elab_toAttributeKind(x_5, x_11, x_12);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
x_15 = l_Lean_Macro_getCurrNamespace(x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(7u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(9u);
x_21 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getArg(x_1, x_20);
x_23 = l_Lean_Syntax_getArg(x_1, x_8);
x_24 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(x_1, x_16, x_9, x_7, x_23, x_6, x_4, x_10, x_21, x_22, x_11, x_17);
lean_dec(x_1);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandNotation", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandNotation), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNotation_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandNotation", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(152u);
x_8 = lean_unsigned_to_nat(46u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(158u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(50u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(64u);
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
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Notation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNotation_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
