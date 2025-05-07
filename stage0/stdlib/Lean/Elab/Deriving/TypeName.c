// Lean compiler output
// Module: Lean.Elab.Deriving.TypeName
// Imports: Lean.Elab.Deriving.Basic
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_TypeName___hyg_688_(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
lean_inc(x_1);
x_12 = l_Lean_Environment_find_x3f(x_9, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
x_13 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_unbox(x_10);
x_16 = l_Lean_MessageData_ofConstName(x_1, x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_20, x_2, x_3, x_8);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_1);
x_28 = l_Lean_Environment_find_x3f(x_25, x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_unbox(x_26);
x_32 = l_Lean_MessageData_ofConstName(x_1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("'", 1, 1);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_36, x_2, x_3, x_24);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_157; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_SourceInfo_fromRef(x_7, x_18);
lean_dec(x_7);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Command", 7, 7);
x_25 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_28 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_27);
x_29 = l_Array_mkArray0(lean_box(0));
lean_inc(x_21);
lean_inc(x_19);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_31);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_32 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_31);
lean_inc(x_19);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 1, x_31);
lean_ctor_set(x_9, 0, x_19);
lean_inc(x_19);
x_33 = l_Lean_Syntax_node1(x_19, x_32, x_9);
lean_inc(x_21);
lean_inc(x_19);
x_34 = l_Lean_Syntax_node1(x_19, x_21, x_33);
lean_inc_n(x_30, 5);
lean_inc(x_28);
lean_inc(x_19);
x_35 = l_Lean_Syntax_node6(x_19, x_28, x_30, x_30, x_30, x_30, x_34, x_30);
x_36 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_37 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_36);
x_38 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_19);
lean_ctor_set_tag(x_5, 2);
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_19);
x_39 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_40 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_39);
x_41 = lean_mk_string_unchecked("instImpl", 8, 8);
lean_inc(x_41);
x_42 = l_String_toSubstring_x27(x_41);
x_43 = l_Lean_Name_mkStr1(x_41);
lean_inc(x_11);
lean_inc(x_14);
x_44 = l_Lean_addMacroScope(x_14, x_43, x_11);
x_45 = lean_box(0);
lean_inc(x_19);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
lean_inc(x_30);
lean_inc(x_46);
lean_inc(x_40);
lean_inc(x_19);
x_47 = l_Lean_Syntax_node2(x_19, x_40, x_46, x_30);
x_48 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_49 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_48);
x_50 = lean_mk_string_unchecked("Term", 4, 4);
x_51 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_52 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_51);
x_53 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_19);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_56 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_55);
x_57 = lean_mk_string_unchecked("TypeName", 8, 8);
lean_inc(x_57);
x_58 = l_String_toSubstring_x27(x_57);
x_59 = l_Lean_Name_mkStr1(x_57);
lean_inc(x_11);
lean_inc(x_59);
lean_inc(x_14);
x_60 = l_Lean_addMacroScope(x_14, x_59, x_11);
x_61 = lean_box(0);
lean_inc(x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_19);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_19);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_68 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_67);
x_69 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_19);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_19);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_1);
x_71 = l_Lean_mkCIdent(x_1);
lean_inc(x_19);
x_72 = l_Lean_Syntax_node2(x_19, x_68, x_70, x_71);
lean_inc(x_21);
lean_inc(x_19);
x_73 = l_Lean_Syntax_node1(x_19, x_21, x_72);
lean_inc(x_56);
lean_inc(x_19);
x_74 = l_Lean_Syntax_node2(x_19, x_56, x_66, x_73);
lean_inc(x_19);
x_75 = l_Lean_Syntax_node2(x_19, x_52, x_54, x_74);
lean_inc(x_75);
lean_inc(x_21);
lean_inc(x_19);
x_76 = l_Lean_Syntax_node1(x_19, x_21, x_75);
lean_inc(x_30);
lean_inc(x_19);
x_77 = l_Lean_Syntax_node2(x_19, x_49, x_30, x_76);
x_78 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_79 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_78);
x_80 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_19);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_19);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("dotIdent", 8, 8);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_83 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_82);
x_84 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_84);
lean_inc(x_19);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_19);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_86);
x_87 = l_String_toSubstring_x27(x_86);
x_88 = l_Lean_Name_mkStr1(x_86);
lean_inc(x_11);
lean_inc(x_14);
x_89 = l_Lean_addMacroScope(x_14, x_88, x_11);
lean_inc(x_19);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_19);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_45);
lean_inc(x_19);
x_91 = l_Lean_Syntax_node2(x_19, x_83, x_85, x_90);
x_92 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_93 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_92);
x_94 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_19);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_19);
x_96 = l_Lean_Syntax_node1(x_19, x_93, x_95);
lean_inc(x_1);
x_157 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_61, x_1);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
lean_dec(x_84);
x_158 = l_Lean_quoteNameMk(x_1);
x_97 = x_158;
goto block_156;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_1);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_161 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_160);
x_162 = lean_mk_string_unchecked("`", 1, 1);
x_163 = l_String_intercalate(x_84, x_159);
lean_dec(x_84);
x_164 = lean_string_append(x_162, x_163);
lean_dec(x_163);
x_165 = lean_box(2);
x_166 = l_Lean_Syntax_mkNameLit(x_164, x_165);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_mk_empty_array_with_capacity(x_167);
x_169 = lean_array_push(x_168, x_166);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_161);
lean_ctor_set(x_170, 2, x_169);
x_97 = x_170;
goto block_156;
}
block_156:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_inc(x_21);
lean_inc(x_19);
x_98 = l_Lean_Syntax_node2(x_19, x_21, x_96, x_97);
lean_inc(x_19);
x_99 = l_Lean_Syntax_node2(x_19, x_56, x_91, x_98);
x_100 = lean_mk_string_unchecked("Termination", 11, 11);
x_101 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_23);
lean_inc(x_22);
x_102 = l_Lean_Name_mkStr4(x_22, x_23, x_100, x_101);
lean_inc_n(x_30, 2);
lean_inc(x_19);
x_103 = l_Lean_Syntax_node2(x_19, x_102, x_30, x_30);
lean_inc(x_30);
lean_inc(x_103);
lean_inc(x_81);
lean_inc(x_79);
lean_inc(x_19);
x_104 = l_Lean_Syntax_node4(x_19, x_79, x_81, x_99, x_103, x_30);
lean_inc(x_30);
lean_inc(x_19);
x_105 = l_Lean_Syntax_node5(x_19, x_37, x_5, x_47, x_77, x_104, x_30);
lean_inc(x_26);
lean_inc(x_19);
x_106 = l_Lean_Syntax_node2(x_19, x_26, x_35, x_105);
x_107 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_108 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_107);
x_109 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_19);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_19);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_50);
lean_inc(x_23);
lean_inc(x_22);
x_112 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_111);
x_113 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_23);
lean_inc(x_22);
x_114 = l_Lean_Name_mkStr4(x_22, x_23, x_50, x_113);
lean_inc(x_30);
lean_inc(x_19);
x_115 = l_Lean_Syntax_node1(x_19, x_114, x_30);
x_116 = lean_mk_string_unchecked("Attr", 4, 4);
x_117 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_23);
lean_inc(x_22);
x_118 = l_Lean_Name_mkStr4(x_22, x_23, x_116, x_117);
x_119 = lean_mk_string_unchecked("implemented_by", 14, 14);
lean_inc(x_119);
x_120 = l_String_toSubstring_x27(x_119);
x_121 = l_Lean_Name_mkStr1(x_119);
lean_inc(x_11);
lean_inc(x_14);
x_122 = l_Lean_addMacroScope(x_14, x_121, x_11);
lean_inc(x_19);
x_123 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_123, 0, x_19);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_45);
lean_inc(x_21);
lean_inc(x_19);
x_124 = l_Lean_Syntax_node1(x_19, x_21, x_46);
lean_inc(x_19);
x_125 = l_Lean_Syntax_node2(x_19, x_118, x_123, x_124);
lean_inc(x_115);
lean_inc(x_19);
x_126 = l_Lean_Syntax_node2(x_19, x_112, x_115, x_125);
lean_inc(x_21);
lean_inc(x_19);
x_127 = l_Lean_Syntax_node1(x_19, x_21, x_126);
x_128 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_19);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_19);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_19);
x_130 = l_Lean_Syntax_node3(x_19, x_108, x_110, x_127, x_129);
lean_inc(x_21);
lean_inc(x_19);
x_131 = l_Lean_Syntax_node1(x_19, x_21, x_130);
lean_inc_n(x_30, 5);
lean_inc(x_28);
lean_inc(x_19);
x_132 = l_Lean_Syntax_node6(x_19, x_28, x_30, x_131, x_30, x_30, x_30, x_30);
x_133 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_133);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_134 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_133);
lean_inc(x_19);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_19);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_mk_string_unchecked("inst", 4, 4);
lean_inc(x_136);
x_137 = l_String_toSubstring_x27(x_136);
x_138 = l_Lean_Name_mkStr1(x_136);
x_139 = l_Lean_addMacroScope(x_14, x_138, x_11);
lean_inc(x_19);
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_19);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_45);
lean_inc(x_30);
lean_inc(x_140);
lean_inc(x_19);
x_141 = l_Lean_Syntax_node2(x_19, x_40, x_140, x_30);
x_142 = lean_mk_string_unchecked("declSig", 7, 7);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_143 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_142);
lean_inc(x_30);
lean_inc(x_19);
x_144 = l_Lean_Syntax_node2(x_19, x_143, x_30, x_75);
lean_inc(x_30);
lean_inc(x_144);
lean_inc(x_19);
x_145 = l_Lean_Syntax_node4(x_19, x_134, x_135, x_141, x_144, x_30);
lean_inc(x_26);
lean_inc(x_19);
x_146 = l_Lean_Syntax_node2(x_19, x_26, x_132, x_145);
lean_inc_n(x_30, 6);
lean_inc(x_19);
x_147 = l_Lean_Syntax_node6(x_19, x_28, x_30, x_30, x_30, x_30, x_30, x_30);
x_148 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_148);
x_149 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_148);
lean_inc(x_19);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_19);
lean_ctor_set(x_150, 1, x_148);
lean_inc(x_30);
lean_inc(x_19);
x_151 = l_Lean_Syntax_node4(x_19, x_79, x_81, x_140, x_103, x_30);
lean_inc(x_30);
lean_inc(x_19);
x_152 = l_Lean_Syntax_node6(x_19, x_149, x_115, x_150, x_30, x_30, x_144, x_151);
lean_inc(x_19);
x_153 = l_Lean_Syntax_node2(x_19, x_26, x_147, x_152);
x_154 = l_Lean_Syntax_node3(x_19, x_21, x_106, x_146, x_153);
if (lean_is_scalar(x_16)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_16;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_15);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_318; 
x_171 = lean_ctor_get(x_9, 0);
x_172 = lean_ctor_get(x_9, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_9);
x_173 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
x_178 = lean_unbox(x_177);
x_179 = l_Lean_SourceInfo_fromRef(x_7, x_178);
lean_dec(x_7);
x_180 = lean_mk_string_unchecked("null", 4, 4);
x_181 = l_Lean_Name_mkStr1(x_180);
x_182 = lean_mk_string_unchecked("Lean", 4, 4);
x_183 = lean_mk_string_unchecked("Parser", 6, 6);
x_184 = lean_mk_string_unchecked("Command", 7, 7);
x_185 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_186 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_185);
x_187 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_188 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_187);
x_189 = l_Array_mkArray0(lean_box(0));
lean_inc(x_181);
lean_inc(x_179);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_179);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_189);
x_191 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_191);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_192 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_191);
lean_inc(x_179);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_179);
lean_ctor_set(x_193, 1, x_191);
lean_inc(x_179);
x_194 = l_Lean_Syntax_node1(x_179, x_192, x_193);
lean_inc(x_181);
lean_inc(x_179);
x_195 = l_Lean_Syntax_node1(x_179, x_181, x_194);
lean_inc_n(x_190, 5);
lean_inc(x_188);
lean_inc(x_179);
x_196 = l_Lean_Syntax_node6(x_179, x_188, x_190, x_190, x_190, x_190, x_195, x_190);
x_197 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_198 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_197);
x_199 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_179);
lean_ctor_set_tag(x_5, 2);
lean_ctor_set(x_5, 1, x_199);
lean_ctor_set(x_5, 0, x_179);
x_200 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_201 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_200);
x_202 = lean_mk_string_unchecked("instImpl", 8, 8);
lean_inc(x_202);
x_203 = l_String_toSubstring_x27(x_202);
x_204 = l_Lean_Name_mkStr1(x_202);
lean_inc(x_171);
lean_inc(x_174);
x_205 = l_Lean_addMacroScope(x_174, x_204, x_171);
x_206 = lean_box(0);
lean_inc(x_179);
x_207 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_207, 0, x_179);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_205);
lean_ctor_set(x_207, 3, x_206);
lean_inc(x_190);
lean_inc(x_207);
lean_inc(x_201);
lean_inc(x_179);
x_208 = l_Lean_Syntax_node2(x_179, x_201, x_207, x_190);
x_209 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_210 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_209);
x_211 = lean_mk_string_unchecked("Term", 4, 4);
x_212 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_213 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_212);
x_214 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_179);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_179);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_217 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_216);
x_218 = lean_mk_string_unchecked("TypeName", 8, 8);
lean_inc(x_218);
x_219 = l_String_toSubstring_x27(x_218);
x_220 = l_Lean_Name_mkStr1(x_218);
lean_inc(x_171);
lean_inc(x_220);
lean_inc(x_174);
x_221 = l_Lean_addMacroScope(x_174, x_220, x_171);
x_222 = lean_box(0);
lean_inc(x_220);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_220);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_206);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_179);
x_227 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_227, 0, x_179);
lean_ctor_set(x_227, 1, x_219);
lean_ctor_set(x_227, 2, x_221);
lean_ctor_set(x_227, 3, x_226);
x_228 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_229 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_228);
x_230 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_179);
x_231 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_231, 0, x_179);
lean_ctor_set(x_231, 1, x_230);
lean_inc(x_1);
x_232 = l_Lean_mkCIdent(x_1);
lean_inc(x_179);
x_233 = l_Lean_Syntax_node2(x_179, x_229, x_231, x_232);
lean_inc(x_181);
lean_inc(x_179);
x_234 = l_Lean_Syntax_node1(x_179, x_181, x_233);
lean_inc(x_217);
lean_inc(x_179);
x_235 = l_Lean_Syntax_node2(x_179, x_217, x_227, x_234);
lean_inc(x_179);
x_236 = l_Lean_Syntax_node2(x_179, x_213, x_215, x_235);
lean_inc(x_236);
lean_inc(x_181);
lean_inc(x_179);
x_237 = l_Lean_Syntax_node1(x_179, x_181, x_236);
lean_inc(x_190);
lean_inc(x_179);
x_238 = l_Lean_Syntax_node2(x_179, x_210, x_190, x_237);
x_239 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_240 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_239);
x_241 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_179);
x_242 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_242, 0, x_179);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_mk_string_unchecked("dotIdent", 8, 8);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_244 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_243);
x_245 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_245);
lean_inc(x_179);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_179);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_247);
x_248 = l_String_toSubstring_x27(x_247);
x_249 = l_Lean_Name_mkStr1(x_247);
lean_inc(x_171);
lean_inc(x_174);
x_250 = l_Lean_addMacroScope(x_174, x_249, x_171);
lean_inc(x_179);
x_251 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_251, 0, x_179);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_250);
lean_ctor_set(x_251, 3, x_206);
lean_inc(x_179);
x_252 = l_Lean_Syntax_node2(x_179, x_244, x_246, x_251);
x_253 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_254 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_253);
x_255 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_179);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_179);
lean_ctor_set(x_256, 1, x_255);
lean_inc(x_179);
x_257 = l_Lean_Syntax_node1(x_179, x_254, x_256);
lean_inc(x_1);
x_318 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_222, x_1);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
lean_dec(x_245);
x_319 = l_Lean_quoteNameMk(x_1);
x_258 = x_319;
goto block_317;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_1);
x_320 = lean_ctor_get(x_318, 0);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_322 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_321);
x_323 = lean_mk_string_unchecked("`", 1, 1);
x_324 = l_String_intercalate(x_245, x_320);
lean_dec(x_245);
x_325 = lean_string_append(x_323, x_324);
lean_dec(x_324);
x_326 = lean_box(2);
x_327 = l_Lean_Syntax_mkNameLit(x_325, x_326);
x_328 = lean_unsigned_to_nat(1u);
x_329 = lean_mk_empty_array_with_capacity(x_328);
x_330 = lean_array_push(x_329, x_327);
x_331 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_331, 0, x_326);
lean_ctor_set(x_331, 1, x_322);
lean_ctor_set(x_331, 2, x_330);
x_258 = x_331;
goto block_317;
}
block_317:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_inc(x_181);
lean_inc(x_179);
x_259 = l_Lean_Syntax_node2(x_179, x_181, x_257, x_258);
lean_inc(x_179);
x_260 = l_Lean_Syntax_node2(x_179, x_217, x_252, x_259);
x_261 = lean_mk_string_unchecked("Termination", 11, 11);
x_262 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_183);
lean_inc(x_182);
x_263 = l_Lean_Name_mkStr4(x_182, x_183, x_261, x_262);
lean_inc_n(x_190, 2);
lean_inc(x_179);
x_264 = l_Lean_Syntax_node2(x_179, x_263, x_190, x_190);
lean_inc(x_190);
lean_inc(x_264);
lean_inc(x_242);
lean_inc(x_240);
lean_inc(x_179);
x_265 = l_Lean_Syntax_node4(x_179, x_240, x_242, x_260, x_264, x_190);
lean_inc(x_190);
lean_inc(x_179);
x_266 = l_Lean_Syntax_node5(x_179, x_198, x_5, x_208, x_238, x_265, x_190);
lean_inc(x_186);
lean_inc(x_179);
x_267 = l_Lean_Syntax_node2(x_179, x_186, x_196, x_266);
x_268 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_269 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_268);
x_270 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_179);
x_271 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_271, 0, x_179);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_211);
lean_inc(x_183);
lean_inc(x_182);
x_273 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_272);
x_274 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_183);
lean_inc(x_182);
x_275 = l_Lean_Name_mkStr4(x_182, x_183, x_211, x_274);
lean_inc(x_190);
lean_inc(x_179);
x_276 = l_Lean_Syntax_node1(x_179, x_275, x_190);
x_277 = lean_mk_string_unchecked("Attr", 4, 4);
x_278 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_183);
lean_inc(x_182);
x_279 = l_Lean_Name_mkStr4(x_182, x_183, x_277, x_278);
x_280 = lean_mk_string_unchecked("implemented_by", 14, 14);
lean_inc(x_280);
x_281 = l_String_toSubstring_x27(x_280);
x_282 = l_Lean_Name_mkStr1(x_280);
lean_inc(x_171);
lean_inc(x_174);
x_283 = l_Lean_addMacroScope(x_174, x_282, x_171);
lean_inc(x_179);
x_284 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_284, 0, x_179);
lean_ctor_set(x_284, 1, x_281);
lean_ctor_set(x_284, 2, x_283);
lean_ctor_set(x_284, 3, x_206);
lean_inc(x_181);
lean_inc(x_179);
x_285 = l_Lean_Syntax_node1(x_179, x_181, x_207);
lean_inc(x_179);
x_286 = l_Lean_Syntax_node2(x_179, x_279, x_284, x_285);
lean_inc(x_276);
lean_inc(x_179);
x_287 = l_Lean_Syntax_node2(x_179, x_273, x_276, x_286);
lean_inc(x_181);
lean_inc(x_179);
x_288 = l_Lean_Syntax_node1(x_179, x_181, x_287);
x_289 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_179);
x_290 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_290, 0, x_179);
lean_ctor_set(x_290, 1, x_289);
lean_inc(x_179);
x_291 = l_Lean_Syntax_node3(x_179, x_269, x_271, x_288, x_290);
lean_inc(x_181);
lean_inc(x_179);
x_292 = l_Lean_Syntax_node1(x_179, x_181, x_291);
lean_inc_n(x_190, 5);
lean_inc(x_188);
lean_inc(x_179);
x_293 = l_Lean_Syntax_node6(x_179, x_188, x_190, x_292, x_190, x_190, x_190, x_190);
x_294 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_294);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_295 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_294);
lean_inc(x_179);
x_296 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_296, 0, x_179);
lean_ctor_set(x_296, 1, x_294);
x_297 = lean_mk_string_unchecked("inst", 4, 4);
lean_inc(x_297);
x_298 = l_String_toSubstring_x27(x_297);
x_299 = l_Lean_Name_mkStr1(x_297);
x_300 = l_Lean_addMacroScope(x_174, x_299, x_171);
lean_inc(x_179);
x_301 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_301, 0, x_179);
lean_ctor_set(x_301, 1, x_298);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set(x_301, 3, x_206);
lean_inc(x_190);
lean_inc(x_301);
lean_inc(x_179);
x_302 = l_Lean_Syntax_node2(x_179, x_201, x_301, x_190);
x_303 = lean_mk_string_unchecked("declSig", 7, 7);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_304 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_303);
lean_inc(x_190);
lean_inc(x_179);
x_305 = l_Lean_Syntax_node2(x_179, x_304, x_190, x_236);
lean_inc(x_190);
lean_inc(x_305);
lean_inc(x_179);
x_306 = l_Lean_Syntax_node4(x_179, x_295, x_296, x_302, x_305, x_190);
lean_inc(x_186);
lean_inc(x_179);
x_307 = l_Lean_Syntax_node2(x_179, x_186, x_293, x_306);
lean_inc_n(x_190, 6);
lean_inc(x_179);
x_308 = l_Lean_Syntax_node6(x_179, x_188, x_190, x_190, x_190, x_190, x_190, x_190);
x_309 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_309);
x_310 = l_Lean_Name_mkStr4(x_182, x_183, x_184, x_309);
lean_inc(x_179);
x_311 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_311, 0, x_179);
lean_ctor_set(x_311, 1, x_309);
lean_inc(x_190);
lean_inc(x_179);
x_312 = l_Lean_Syntax_node4(x_179, x_240, x_242, x_301, x_264, x_190);
lean_inc(x_190);
lean_inc(x_179);
x_313 = l_Lean_Syntax_node6(x_179, x_310, x_276, x_311, x_190, x_190, x_305, x_312);
lean_inc(x_179);
x_314 = l_Lean_Syntax_node2(x_179, x_186, x_308, x_313);
x_315 = l_Lean_Syntax_node3(x_179, x_181, x_267, x_307, x_314);
if (lean_is_scalar(x_176)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_176;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_175);
return x_316;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_484; 
x_332 = lean_ctor_get(x_5, 0);
x_333 = lean_ctor_get(x_5, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_5);
x_334 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_336);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
x_342 = lean_box(0);
x_343 = lean_unbox(x_342);
x_344 = l_Lean_SourceInfo_fromRef(x_332, x_343);
lean_dec(x_332);
x_345 = lean_mk_string_unchecked("null", 4, 4);
x_346 = l_Lean_Name_mkStr1(x_345);
x_347 = lean_mk_string_unchecked("Lean", 4, 4);
x_348 = lean_mk_string_unchecked("Parser", 6, 6);
x_349 = lean_mk_string_unchecked("Command", 7, 7);
x_350 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_351 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_350);
x_352 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_353 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_352);
x_354 = l_Array_mkArray0(lean_box(0));
lean_inc(x_346);
lean_inc(x_344);
x_355 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_355, 0, x_344);
lean_ctor_set(x_355, 1, x_346);
lean_ctor_set(x_355, 2, x_354);
x_356 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_356);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_357 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_356);
lean_inc(x_344);
if (lean_is_scalar(x_337)) {
 x_358 = lean_alloc_ctor(2, 2, 0);
} else {
 x_358 = x_337;
 lean_ctor_set_tag(x_358, 2);
}
lean_ctor_set(x_358, 0, x_344);
lean_ctor_set(x_358, 1, x_356);
lean_inc(x_344);
x_359 = l_Lean_Syntax_node1(x_344, x_357, x_358);
lean_inc(x_346);
lean_inc(x_344);
x_360 = l_Lean_Syntax_node1(x_344, x_346, x_359);
lean_inc_n(x_355, 5);
lean_inc(x_353);
lean_inc(x_344);
x_361 = l_Lean_Syntax_node6(x_344, x_353, x_355, x_355, x_355, x_355, x_360, x_355);
x_362 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_363 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_362);
x_364 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_344);
x_365 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_365, 0, x_344);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_367 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_366);
x_368 = lean_mk_string_unchecked("instImpl", 8, 8);
lean_inc(x_368);
x_369 = l_String_toSubstring_x27(x_368);
x_370 = l_Lean_Name_mkStr1(x_368);
lean_inc(x_335);
lean_inc(x_339);
x_371 = l_Lean_addMacroScope(x_339, x_370, x_335);
x_372 = lean_box(0);
lean_inc(x_344);
x_373 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_373, 0, x_344);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_371);
lean_ctor_set(x_373, 3, x_372);
lean_inc(x_355);
lean_inc(x_373);
lean_inc(x_367);
lean_inc(x_344);
x_374 = l_Lean_Syntax_node2(x_344, x_367, x_373, x_355);
x_375 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_376 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_375);
x_377 = lean_mk_string_unchecked("Term", 4, 4);
x_378 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_379 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_378);
x_380 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_344);
x_381 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_381, 0, x_344);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_383 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_382);
x_384 = lean_mk_string_unchecked("TypeName", 8, 8);
lean_inc(x_384);
x_385 = l_String_toSubstring_x27(x_384);
x_386 = l_Lean_Name_mkStr1(x_384);
lean_inc(x_335);
lean_inc(x_386);
lean_inc(x_339);
x_387 = l_Lean_addMacroScope(x_339, x_386, x_335);
x_388 = lean_box(0);
lean_inc(x_386);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_390, 0, x_386);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_372);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
lean_inc(x_344);
x_393 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_393, 0, x_344);
lean_ctor_set(x_393, 1, x_385);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_392);
x_394 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_395 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_394);
x_396 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_344);
x_397 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_397, 0, x_344);
lean_ctor_set(x_397, 1, x_396);
lean_inc(x_1);
x_398 = l_Lean_mkCIdent(x_1);
lean_inc(x_344);
x_399 = l_Lean_Syntax_node2(x_344, x_395, x_397, x_398);
lean_inc(x_346);
lean_inc(x_344);
x_400 = l_Lean_Syntax_node1(x_344, x_346, x_399);
lean_inc(x_383);
lean_inc(x_344);
x_401 = l_Lean_Syntax_node2(x_344, x_383, x_393, x_400);
lean_inc(x_344);
x_402 = l_Lean_Syntax_node2(x_344, x_379, x_381, x_401);
lean_inc(x_402);
lean_inc(x_346);
lean_inc(x_344);
x_403 = l_Lean_Syntax_node1(x_344, x_346, x_402);
lean_inc(x_355);
lean_inc(x_344);
x_404 = l_Lean_Syntax_node2(x_344, x_376, x_355, x_403);
x_405 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_406 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_405);
x_407 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_344);
x_408 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_408, 0, x_344);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_mk_string_unchecked("dotIdent", 8, 8);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_410 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_409);
x_411 = lean_mk_string_unchecked(".", 1, 1);
lean_inc(x_411);
lean_inc(x_344);
x_412 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_412, 0, x_344);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_413);
x_414 = l_String_toSubstring_x27(x_413);
x_415 = l_Lean_Name_mkStr1(x_413);
lean_inc(x_335);
lean_inc(x_339);
x_416 = l_Lean_addMacroScope(x_339, x_415, x_335);
lean_inc(x_344);
x_417 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_417, 0, x_344);
lean_ctor_set(x_417, 1, x_414);
lean_ctor_set(x_417, 2, x_416);
lean_ctor_set(x_417, 3, x_372);
lean_inc(x_344);
x_418 = l_Lean_Syntax_node2(x_344, x_410, x_412, x_417);
x_419 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_420 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_419);
x_421 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_344);
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_344);
lean_ctor_set(x_422, 1, x_421);
lean_inc(x_344);
x_423 = l_Lean_Syntax_node1(x_344, x_420, x_422);
lean_inc(x_1);
x_484 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_388, x_1);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
lean_dec(x_411);
x_485 = l_Lean_quoteNameMk(x_1);
x_424 = x_485;
goto block_483;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_1);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec(x_484);
x_487 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_488 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_487);
x_489 = lean_mk_string_unchecked("`", 1, 1);
x_490 = l_String_intercalate(x_411, x_486);
lean_dec(x_411);
x_491 = lean_string_append(x_489, x_490);
lean_dec(x_490);
x_492 = lean_box(2);
x_493 = l_Lean_Syntax_mkNameLit(x_491, x_492);
x_494 = lean_unsigned_to_nat(1u);
x_495 = lean_mk_empty_array_with_capacity(x_494);
x_496 = lean_array_push(x_495, x_493);
x_497 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_497, 0, x_492);
lean_ctor_set(x_497, 1, x_488);
lean_ctor_set(x_497, 2, x_496);
x_424 = x_497;
goto block_483;
}
block_483:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_inc(x_346);
lean_inc(x_344);
x_425 = l_Lean_Syntax_node2(x_344, x_346, x_423, x_424);
lean_inc(x_344);
x_426 = l_Lean_Syntax_node2(x_344, x_383, x_418, x_425);
x_427 = lean_mk_string_unchecked("Termination", 11, 11);
x_428 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_348);
lean_inc(x_347);
x_429 = l_Lean_Name_mkStr4(x_347, x_348, x_427, x_428);
lean_inc_n(x_355, 2);
lean_inc(x_344);
x_430 = l_Lean_Syntax_node2(x_344, x_429, x_355, x_355);
lean_inc(x_355);
lean_inc(x_430);
lean_inc(x_408);
lean_inc(x_406);
lean_inc(x_344);
x_431 = l_Lean_Syntax_node4(x_344, x_406, x_408, x_426, x_430, x_355);
lean_inc(x_355);
lean_inc(x_344);
x_432 = l_Lean_Syntax_node5(x_344, x_363, x_365, x_374, x_404, x_431, x_355);
lean_inc(x_351);
lean_inc(x_344);
x_433 = l_Lean_Syntax_node2(x_344, x_351, x_361, x_432);
x_434 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_435 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_434);
x_436 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_344);
x_437 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_437, 0, x_344);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_377);
lean_inc(x_348);
lean_inc(x_347);
x_439 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_438);
x_440 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_348);
lean_inc(x_347);
x_441 = l_Lean_Name_mkStr4(x_347, x_348, x_377, x_440);
lean_inc(x_355);
lean_inc(x_344);
x_442 = l_Lean_Syntax_node1(x_344, x_441, x_355);
x_443 = lean_mk_string_unchecked("Attr", 4, 4);
x_444 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_348);
lean_inc(x_347);
x_445 = l_Lean_Name_mkStr4(x_347, x_348, x_443, x_444);
x_446 = lean_mk_string_unchecked("implemented_by", 14, 14);
lean_inc(x_446);
x_447 = l_String_toSubstring_x27(x_446);
x_448 = l_Lean_Name_mkStr1(x_446);
lean_inc(x_335);
lean_inc(x_339);
x_449 = l_Lean_addMacroScope(x_339, x_448, x_335);
lean_inc(x_344);
x_450 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_450, 0, x_344);
lean_ctor_set(x_450, 1, x_447);
lean_ctor_set(x_450, 2, x_449);
lean_ctor_set(x_450, 3, x_372);
lean_inc(x_346);
lean_inc(x_344);
x_451 = l_Lean_Syntax_node1(x_344, x_346, x_373);
lean_inc(x_344);
x_452 = l_Lean_Syntax_node2(x_344, x_445, x_450, x_451);
lean_inc(x_442);
lean_inc(x_344);
x_453 = l_Lean_Syntax_node2(x_344, x_439, x_442, x_452);
lean_inc(x_346);
lean_inc(x_344);
x_454 = l_Lean_Syntax_node1(x_344, x_346, x_453);
x_455 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_344);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_344);
lean_ctor_set(x_456, 1, x_455);
lean_inc(x_344);
x_457 = l_Lean_Syntax_node3(x_344, x_435, x_437, x_454, x_456);
lean_inc(x_346);
lean_inc(x_344);
x_458 = l_Lean_Syntax_node1(x_344, x_346, x_457);
lean_inc_n(x_355, 5);
lean_inc(x_353);
lean_inc(x_344);
x_459 = l_Lean_Syntax_node6(x_344, x_353, x_355, x_458, x_355, x_355, x_355, x_355);
x_460 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_460);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_461 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_460);
lean_inc(x_344);
x_462 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_462, 0, x_344);
lean_ctor_set(x_462, 1, x_460);
x_463 = lean_mk_string_unchecked("inst", 4, 4);
lean_inc(x_463);
x_464 = l_String_toSubstring_x27(x_463);
x_465 = l_Lean_Name_mkStr1(x_463);
x_466 = l_Lean_addMacroScope(x_339, x_465, x_335);
lean_inc(x_344);
x_467 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_467, 0, x_344);
lean_ctor_set(x_467, 1, x_464);
lean_ctor_set(x_467, 2, x_466);
lean_ctor_set(x_467, 3, x_372);
lean_inc(x_355);
lean_inc(x_467);
lean_inc(x_344);
x_468 = l_Lean_Syntax_node2(x_344, x_367, x_467, x_355);
x_469 = lean_mk_string_unchecked("declSig", 7, 7);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
x_470 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_469);
lean_inc(x_355);
lean_inc(x_344);
x_471 = l_Lean_Syntax_node2(x_344, x_470, x_355, x_402);
lean_inc(x_355);
lean_inc(x_471);
lean_inc(x_344);
x_472 = l_Lean_Syntax_node4(x_344, x_461, x_462, x_468, x_471, x_355);
lean_inc(x_351);
lean_inc(x_344);
x_473 = l_Lean_Syntax_node2(x_344, x_351, x_459, x_472);
lean_inc_n(x_355, 6);
lean_inc(x_344);
x_474 = l_Lean_Syntax_node6(x_344, x_353, x_355, x_355, x_355, x_355, x_355, x_355);
x_475 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_475);
x_476 = l_Lean_Name_mkStr4(x_347, x_348, x_349, x_475);
lean_inc(x_344);
x_477 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_477, 0, x_344);
lean_ctor_set(x_477, 1, x_475);
lean_inc(x_355);
lean_inc(x_344);
x_478 = l_Lean_Syntax_node4(x_344, x_406, x_408, x_467, x_430, x_355);
lean_inc(x_355);
lean_inc(x_344);
x_479 = l_Lean_Syntax_node6(x_344, x_476, x_442, x_477, x_355, x_355, x_471, x_478);
lean_inc(x_344);
x_480 = l_Lean_Syntax_node2(x_344, x_351, x_474, x_479);
x_481 = l_Lean_Syntax_node3(x_344, x_346, x_433, x_473, x_480);
if (lean_is_scalar(x_341)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_341;
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_340);
return x_482;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_10);
x_11 = l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_33; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(x_15, 0, x_10);
x_33 = l_Lean_ConstantInfo_levelParams(x_12);
lean_dec(x_12);
x_34 = l_List_isEmpty___redArg(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_MessageData_ofConstName(x_10, x_34);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked(" has universe level parameters", 30, 30);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_41, x_5, x_6, x_13);
lean_dec(x_6);
return x_42;
}
else
{
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
x_16 = x_5;
x_17 = x_6;
x_18 = x_13;
goto block_32;
}
block_32:
{
lean_object* x_19; 
lean_inc(x_17);
x_19 = l_Lean_Elab_Command_withFreshMacroScope(lean_box(0), x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Command_elabCommand(x_20, x_16, x_17, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_4 = x_14;
x_7 = x_23;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_array_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(x_1, x_6, x_8, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_TypeName___hyg_688_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("TypeName", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed), 4, 0);
x_5 = l_Lean_Elab_registerDerivingHandler(x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_TypeName___hyg_688_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
