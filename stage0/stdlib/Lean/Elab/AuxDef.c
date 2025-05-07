// Lean compiler output
// Module: Lean.Elab.AuxDef
// Imports: Lean.Elab.Command
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAuxDef__1(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_aux__def;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0(uint8_t, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0(size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_aux__def() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("Command", 7, 7);
x_4 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("docComment", 10, 10);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_18 = l_Lean_Name_mkStr4(x_1, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_4);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("many1", 5, 5);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("ident", 5, 5);
x_27 = l_Lean_Name_mkStr4(x_1, x_15, x_16, x_26);
x_28 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked(":", 1, 1);
x_32 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_8);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked("term", 4, 4);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_37);
lean_inc(x_8);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_mk_string_unchecked(":=", 2, 2);
x_40 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_8);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_37);
x_43 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_6);
lean_ctor_set(x_43, 2, x_42);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
x_9 = lean_erase_macro_scopes(x_8);
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
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_Name_toString(x_5, x_9, x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_Name_toString(x_12, x_16, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_8, x_1, x_2);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Name_append(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_7);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_140; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_140 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_185; uint8_t x_186; 
x_141 = lean_unsigned_to_nat(0u);
x_185 = l_Lean_Syntax_getArg(x_1, x_141);
x_186 = l_Lean_Syntax_isNone(x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_unsigned_to_nat(1u);
lean_inc(x_185);
x_188 = l_Lean_Syntax_matchesNull(x_185, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_185);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_189 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = l_Lean_Syntax_getArg(x_185, x_141);
lean_dec(x_185);
x_191 = lean_mk_string_unchecked("Parser", 6, 6);
x_192 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_5);
x_193 = l_Lean_Name_mkStr4(x_5, x_191, x_7, x_192);
lean_inc(x_190);
x_194 = l_Lean_Syntax_isOfKind(x_190, x_193);
lean_dec(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_190);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_195 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_190);
x_166 = x_196;
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
goto block_184;
}
}
}
else
{
lean_object* x_197; 
lean_dec(x_185);
x_197 = lean_box(0);
x_166 = x_197;
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
goto block_184;
}
block_165:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; size_t x_154; lean_object* x_155; lean_object* x_156; size_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_148 = lean_unsigned_to_nat(3u);
x_149 = l_Lean_Syntax_getArg(x_1, x_148);
x_150 = l_Lean_Elab_Command_getMainModule___redArg(x_146, x_147);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Syntax_getArgs(x_149);
lean_dec(x_149);
x_154 = lean_array_size(x_153);
x_155 = lean_unsigned_to_nat(5u);
x_156 = lean_unsigned_to_nat(7u);
x_157 = lean_usize_of_nat(x_141);
lean_inc(x_153);
x_158 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0(x_154, x_157, x_153);
x_159 = lean_array_get_size(x_158);
x_160 = lean_box(0);
x_161 = lean_nat_dec_lt(x_141, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_84 = x_160;
x_85 = x_146;
x_86 = x_142;
x_87 = x_155;
x_88 = x_156;
x_89 = x_144;
x_90 = x_151;
x_91 = x_145;
x_92 = x_152;
x_93 = x_143;
x_94 = x_153;
x_95 = x_160;
goto block_139;
}
else
{
uint8_t x_162; 
x_162 = lean_nat_dec_le(x_159, x_159);
if (x_162 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_84 = x_160;
x_85 = x_146;
x_86 = x_142;
x_87 = x_155;
x_88 = x_156;
x_89 = x_144;
x_90 = x_151;
x_91 = x_145;
x_92 = x_152;
x_93 = x_143;
x_94 = x_153;
x_95 = x_160;
goto block_139;
}
else
{
size_t x_163; lean_object* x_164; 
x_163 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_164 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3(x_158, x_157, x_163, x_160);
lean_dec(x_158);
x_84 = x_160;
x_85 = x_146;
x_86 = x_142;
x_87 = x_155;
x_88 = x_156;
x_89 = x_144;
x_90 = x_151;
x_91 = x_145;
x_92 = x_152;
x_93 = x_143;
x_94 = x_153;
x_95 = x_164;
goto block_139;
}
}
}
block_184:
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_unsigned_to_nat(1u);
x_171 = l_Lean_Syntax_getArg(x_1, x_170);
x_172 = l_Lean_Syntax_isNone(x_171);
if (x_172 == 0)
{
uint8_t x_173; 
lean_inc(x_171);
x_173 = l_Lean_Syntax_matchesNull(x_171, x_170);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_174 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_167, x_168, x_169);
lean_dec(x_168);
lean_dec(x_167);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = l_Lean_Syntax_getArg(x_171, x_141);
lean_dec(x_171);
x_176 = lean_mk_string_unchecked("Parser", 6, 6);
x_177 = lean_mk_string_unchecked("Term", 4, 4);
x_178 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_5);
x_179 = l_Lean_Name_mkStr4(x_5, x_176, x_177, x_178);
lean_inc(x_175);
x_180 = l_Lean_Syntax_isOfKind(x_175, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_175);
lean_dec(x_166);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_181 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_167, x_168, x_169);
lean_dec(x_168);
lean_dec(x_167);
return x_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_175);
x_142 = x_170;
x_143 = x_166;
x_144 = x_182;
x_145 = x_167;
x_146 = x_168;
x_147 = x_169;
goto block_165;
}
}
}
else
{
lean_object* x_183; 
lean_dec(x_171);
x_183 = lean_box(0);
x_142 = x_170;
x_143 = x_166;
x_144 = x_183;
x_145 = x_167;
x_146 = x_168;
x_147 = x_169;
goto block_165;
}
}
}
block_62:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_inc(x_15);
x_26 = l_Array_append(lean_box(0), x_15, x_25);
lean_dec(x_25);
lean_inc(x_23);
lean_inc(x_14);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_23);
lean_inc(x_14);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_15);
lean_inc_n(x_28, 4);
lean_inc(x_14);
x_29 = l_Lean_Syntax_node6(x_14, x_11, x_21, x_27, x_28, x_28, x_28, x_28);
x_30 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_5);
x_31 = l_Lean_Name_mkStr4(x_5, x_20, x_7, x_30);
x_32 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_14);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_5);
x_35 = l_Lean_Name_mkStr4(x_5, x_20, x_7, x_34);
x_36 = lean_box(2);
lean_inc(x_23);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_17);
x_38 = l_Lean_mkIdentFrom(x_37, x_24, x_10);
lean_dec(x_37);
lean_inc(x_28);
lean_inc(x_14);
x_39 = l_Lean_Syntax_node2(x_14, x_35, x_38, x_28);
x_40 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_5);
x_41 = l_Lean_Name_mkStr4(x_5, x_20, x_7, x_40);
x_42 = lean_mk_string_unchecked("Term", 4, 4);
x_43 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_20);
lean_inc(x_5);
x_44 = l_Lean_Name_mkStr4(x_5, x_20, x_42, x_43);
x_45 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_14);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_14);
x_47 = l_Lean_Syntax_node2(x_14, x_44, x_46, x_18);
lean_inc(x_14);
x_48 = l_Lean_Syntax_node1(x_14, x_23, x_47);
lean_inc(x_28);
lean_inc(x_14);
x_49 = l_Lean_Syntax_node2(x_14, x_41, x_28, x_48);
x_50 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_20);
lean_inc(x_5);
x_51 = l_Lean_Name_mkStr4(x_5, x_20, x_7, x_50);
x_52 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_14);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("Termination", 11, 11);
x_55 = lean_mk_string_unchecked("suffix", 6, 6);
x_56 = l_Lean_Name_mkStr4(x_5, x_20, x_54, x_55);
lean_inc_n(x_28, 2);
lean_inc(x_14);
x_57 = l_Lean_Syntax_node2(x_14, x_56, x_28, x_28);
lean_inc(x_28);
lean_inc(x_14);
x_58 = l_Lean_Syntax_node4(x_14, x_51, x_53, x_22, x_57, x_28);
lean_inc(x_14);
x_59 = l_Lean_Syntax_node5(x_14, x_31, x_33, x_39, x_49, x_58, x_28);
x_60 = l_Lean_Syntax_node2(x_14, x_13, x_29, x_59);
x_61 = l_Lean_Elab_Command_elabCommand(x_60, x_16, x_12, x_19);
return x_61;
}
block_83:
{
lean_object* x_78; lean_object* x_79; 
lean_inc(x_67);
x_78 = l_Array_append(lean_box(0), x_67, x_77);
lean_dec(x_77);
lean_inc(x_75);
lean_inc(x_66);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_78);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_80; 
x_80 = l_Array_empty(lean_box(0));
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_79;
x_22 = x_74;
x_23 = x_75;
x_24 = x_76;
x_25 = x_80;
goto block_62;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
lean_dec(x_73);
x_82 = l_Array_mkArray1___redArg(x_81);
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_79;
x_22 = x_74;
x_23 = x_75;
x_24 = x_76;
x_25 = x_82;
goto block_62;
}
}
block_139:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_96 = lean_mk_string_unchecked("_aux", 4, 4);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = l_Lean_Name_append(x_97, x_90);
x_99 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_99);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Lean_Name_append(x_98, x_100);
x_102 = l_Lean_Elab_Command_getScope___redArg(x_85, x_92);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Name_append(x_101, x_95);
x_106 = l_Lean_Name_components(x_105);
x_107 = lean_box(0);
x_108 = l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1(x_106, x_107);
x_109 = l_String_intercalate(x_99, x_108);
lean_dec(x_99);
x_110 = lean_ctor_get(x_103, 2);
lean_inc(x_110);
lean_dec(x_103);
lean_inc(x_110);
x_111 = l_Lean_Name_str___override(x_110, x_109);
x_112 = l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg(x_111, x_86, x_85, x_104);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Elab_Command_getRef(x_91, x_85, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Elab_Command_getCurrMacroScope(x_91, x_85, x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_Lean_Elab_Command_getMainModule___redArg(x_85, x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = l_Lean_Syntax_getArg(x_1, x_87);
x_124 = l_Lean_Syntax_getArg(x_1, x_88);
lean_dec(x_1);
x_125 = l_Lean_Name_replacePrefix(x_113, x_110, x_84);
lean_dec(x_110);
x_126 = lean_unbox(x_122);
x_127 = l_Lean_SourceInfo_fromRef(x_116, x_126);
lean_dec(x_116);
x_128 = lean_mk_string_unchecked("Parser", 6, 6);
x_129 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_7);
lean_inc(x_128);
lean_inc(x_5);
x_130 = l_Lean_Name_mkStr4(x_5, x_128, x_7, x_129);
x_131 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_7);
lean_inc(x_128);
lean_inc(x_5);
x_132 = l_Lean_Name_mkStr4(x_5, x_128, x_7, x_131);
x_133 = lean_mk_string_unchecked("null", 4, 4);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_136; 
x_136 = l_Array_empty(lean_box(0));
x_63 = x_132;
x_64 = x_85;
x_65 = x_130;
x_66 = x_127;
x_67 = x_135;
x_68 = x_91;
x_69 = x_94;
x_70 = x_123;
x_71 = x_121;
x_72 = x_128;
x_73 = x_89;
x_74 = x_124;
x_75 = x_134;
x_76 = x_125;
x_77 = x_136;
goto block_83;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_93, 0);
lean_inc(x_137);
lean_dec(x_93);
x_138 = l_Array_mkArray1___redArg(x_137);
x_63 = x_132;
x_64 = x_85;
x_65 = x_130;
x_66 = x_127;
x_67 = x_135;
x_68 = x_91;
x_69 = x_94;
x_70 = x_123;
x_71 = x_121;
x_72 = x_128;
x_73 = x_89;
x_74 = x_124;
x_75 = x_134;
x_76 = x_125;
x_77 = x_138;
goto block_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabAuxDef_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_mapTR_loop___at___Lean_Elab_Command_elabAuxDef_spec__1___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxName___at___Lean_Elab_Command_elabAuxDef_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_elabAuxDef_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAuxDef__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Elab", 4, 4);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("elabAuxDef", 10, 10);
x_9 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAuxDef), 4, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabAuxDef", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(21u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(33u);
x_11 = lean_unsigned_to_nat(31u);
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
x_16 = lean_unsigned_to_nat(14u);
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
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_aux__def = _init_l_Lean_Elab_Command_aux__def();
lean_mark_persistent(l_Lean_Elab_Command_aux__def);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAuxDef__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
