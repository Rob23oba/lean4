// Lean compiler output
// Module: Lake.DSL.Key
// Imports: Lake.Build.Key Lake.DSL.Syntax
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0(size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_PartialBuildKey_moduleTargetIndicator;
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x40_______x2f__________1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Syntax_getId(x_5);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lake_Name_quoteFrom(x_5, x_8, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = l_Lean_SourceInfo_fromRef(x_8, x_7);
lean_dec(x_8);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("app", 3, 3);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_mk_string_unchecked("BuildKey.facet", 14, 14);
x_18 = l_String_toSubstring_x27(x_17);
x_19 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_20 = lean_mk_string_unchecked("facet", 5, 5);
lean_inc(x_20);
lean_inc(x_19);
x_21 = l_Lean_Name_mkStr2(x_19, x_20);
x_22 = l_Lean_addMacroScope(x_11, x_21, x_10);
x_23 = lean_mk_string_unchecked("Lake", 4, 4);
x_24 = l_Lean_Name_mkStr3(x_23, x_19, x_20);
x_25 = lean_box(0);
lean_inc(x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_9);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_array_uget(x_1, x_2);
lean_inc(x_9);
x_35 = l_Lean_Syntax_node2(x_9, x_33, x_4, x_34);
x_36 = l_Lean_Syntax_node2(x_9, x_16, x_31, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_add(x_2, x_38);
x_2 = x_39;
x_4 = x_36;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_array_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(x_5, x_7, x_2);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
size_t x_14; lean_object* x_15; 
x_14 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_15 = l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(x_8, x_7, x_14, x_1, x_3, x_4);
lean_dec(x_8);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lake_DSL_Key_0__Lake_DSL_expandFacets_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_5 = lean_mk_string_unchecked("Lake", 4, 4);
x_53 = lean_mk_string_unchecked("DSL", 3, 3);
x_54 = lean_mk_string_unchecked("packageTargetLit", 16, 16);
lean_inc(x_5);
x_55 = l_Lean_Name_mkStr3(x_5, x_53, x_54);
lean_inc(x_2);
x_56 = l_Lean_Syntax_isOfKind(x_2, x_55);
lean_dec(x_55);
x_57 = lean_ctor_get(x_3, 5);
x_58 = l_Lean_replaceRef(x_2, x_57);
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
x_61 = lean_ctor_get(x_3, 2);
x_62 = lean_ctor_get(x_3, 3);
x_63 = lean_ctor_get(x_3, 4);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_63);
lean_ctor_set(x_64, 5, x_58);
if (x_56 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_mk_string_unchecked("ill-formed package target literal", 33, 33);
x_66 = l_Lean_Macro_throwError___redArg(x_65, x_64, x_4);
lean_dec(x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_Syntax_getArg(x_2, x_67);
x_69 = l_Lean_Syntax_isNone(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_unsigned_to_nat(1u);
lean_inc(x_68);
x_71 = l_Lean_Syntax_matchesNull(x_68, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_mk_string_unchecked("ill-formed package target literal", 33, 33);
x_73 = l_Lean_Macro_throwError___redArg(x_72, x_64, x_4);
lean_dec(x_64);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Syntax_getArg(x_68, x_67);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_43 = x_75;
x_44 = x_64;
x_45 = x_4;
goto block_52;
}
}
else
{
lean_object* x_76; 
lean_dec(x_68);
x_76 = lean_box(0);
x_43 = x_76;
x_44 = x_64;
x_45 = x_4;
goto block_52;
}
}
block_42:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Parser", 6, 6);
x_18 = lean_mk_string_unchecked("Term", 4, 4);
x_19 = lean_mk_string_unchecked("app", 3, 3);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
x_21 = lean_mk_string_unchecked("BuildKey.packageTarget", 22, 22);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_24 = lean_mk_string_unchecked("packageTarget", 13, 13);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
x_26 = l_Lean_addMacroScope(x_15, x_25, x_14);
x_27 = l_Lean_Name_mkStr3(x_5, x_23, x_24);
x_28 = lean_box(0);
lean_inc(x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_13);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_unbox(x_10);
x_38 = l_Lake_Name_quoteFrom(x_7, x_9, x_37);
lean_inc(x_13);
x_39 = l_Lean_Syntax_node2(x_13, x_36, x_1, x_38);
x_40 = l_Lean_Syntax_node2(x_13, x_20, x_34, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
block_52:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Syntax_getArg(x_2, x_46);
lean_dec(x_2);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_48; 
x_48 = l_Lean_Syntax_getId(x_47);
x_6 = x_45;
x_7 = x_47;
x_8 = x_44;
x_9 = x_48;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
x_49 = l_Lean_Syntax_getId(x_47);
x_50 = l_Lake_PartialBuildKey_moduleTargetIndicator;
x_51 = l_Lean_Name_append(x_49, x_50);
x_6 = x_45;
x_7 = x_47;
x_8 = x_44;
x_9 = x_51;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_mk_string_unchecked("Lake", 4, 4);
x_7 = lean_mk_string_unchecked("DSL", 3, 3);
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_mk_string_unchecked("facetSuffix", 11, 11);
x_10 = l_Lean_Name_mkStr3(x_6, x_7, x_9);
lean_inc(x_8);
x_11 = l_Lean_Syntax_isOfKind(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_array_uset(x_3, x_2, x_13);
x_16 = l_Lean_Syntax_getArg(x_8, x_14);
lean_dec(x_8);
x_17 = lean_usize_of_nat(x_14);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_5 = lean_mk_string_unchecked("DSL", 3, 3);
x_6 = lean_mk_string_unchecked("term`+___", 9, 9);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0(x_14, x_16, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = l_Lean_Syntax_getArg(x_1, x_15);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
x_24 = l_Lean_replaceRef(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 4);
lean_inc(x_29);
lean_dec(x_2);
lean_inc(x_27);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_24);
x_31 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_30, x_30, x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
x_37 = l_Lean_Syntax_getId(x_36);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_SourceInfo_fromRef(x_33, x_39);
lean_dec(x_33);
x_41 = lean_mk_string_unchecked("Lean", 4, 4);
x_42 = lean_mk_string_unchecked("Parser", 6, 6);
x_43 = lean_mk_string_unchecked("Term", 4, 4);
x_44 = lean_mk_string_unchecked("app", 3, 3);
x_45 = l_Lean_Name_mkStr4(x_41, x_42, x_43, x_44);
x_46 = lean_mk_string_unchecked("BuildKey.module", 15, 15);
x_47 = l_String_toSubstring_x27(x_46);
x_48 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_49 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_49);
lean_inc(x_48);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
lean_inc(x_27);
lean_inc(x_26);
x_51 = l_Lean_addMacroScope(x_26, x_50, x_27);
lean_inc(x_4);
x_52 = l_Lean_Name_mkStr3(x_4, x_48, x_49);
x_53 = lean_box(0);
lean_inc(x_52);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_53);
lean_ctor_set(x_31, 0, x_52);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_40);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = lean_unbox(x_38);
x_61 = l_Lake_Name_quoteFrom(x_36, x_37, x_60);
lean_inc(x_59);
lean_inc(x_40);
x_62 = l_Lean_Syntax_node1(x_40, x_59, x_61);
lean_inc(x_45);
x_63 = l_Lean_Syntax_node2(x_40, x_45, x_57, x_62);
lean_inc(x_30);
x_64 = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(x_63, x_21, x_30, x_34);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_30, x_30, x_67);
lean_dec(x_30);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_unbox(x_38);
x_72 = l_Lean_SourceInfo_fromRef(x_70, x_71);
lean_dec(x_70);
x_73 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_74 = l_String_toSubstring_x27(x_73);
x_75 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_76 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_76);
lean_inc(x_75);
x_77 = l_Lean_Name_mkStr2(x_75, x_76);
x_78 = l_Lean_addMacroScope(x_26, x_77, x_27);
x_79 = l_Lean_Name_mkStr3(x_4, x_75, x_76);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 0, x_79);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_64);
lean_ctor_set(x_80, 1, x_54);
lean_inc(x_72);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_74);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_80);
lean_inc(x_72);
x_82 = l_Lean_Syntax_node1(x_72, x_59, x_66);
x_83 = l_Lean_Syntax_node2(x_72, x_45, x_81, x_82);
lean_ctor_set(x_68, 0, x_83);
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_84 = lean_ctor_get(x_68, 0);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_68);
x_86 = lean_unbox(x_38);
x_87 = l_Lean_SourceInfo_fromRef(x_84, x_86);
lean_dec(x_84);
x_88 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_89 = l_String_toSubstring_x27(x_88);
x_90 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_91 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_91);
lean_inc(x_90);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_addMacroScope(x_26, x_92, x_27);
x_94 = l_Lean_Name_mkStr3(x_4, x_90, x_91);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 0, x_94);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_54);
lean_inc(x_87);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_95);
lean_inc(x_87);
x_97 = l_Lean_Syntax_node1(x_87, x_59, x_66);
x_98 = l_Lean_Syntax_node2(x_87, x_45, x_96, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_85);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_100 = lean_ctor_get(x_64, 0);
x_101 = lean_ctor_get(x_64, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_64);
x_102 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_30, x_30, x_101);
lean_dec(x_30);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_unbox(x_38);
x_107 = l_Lean_SourceInfo_fromRef(x_103, x_106);
lean_dec(x_103);
x_108 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_109 = l_String_toSubstring_x27(x_108);
x_110 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_111 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_111);
lean_inc(x_110);
x_112 = l_Lean_Name_mkStr2(x_110, x_111);
x_113 = l_Lean_addMacroScope(x_26, x_112, x_27);
x_114 = l_Lean_Name_mkStr3(x_4, x_110, x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_53);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_54);
lean_inc(x_107);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_113);
lean_ctor_set(x_117, 3, x_116);
lean_inc(x_107);
x_118 = l_Lean_Syntax_node1(x_107, x_59, x_100);
x_119 = l_Lean_Syntax_node2(x_107, x_45, x_117, x_118);
if (lean_is_scalar(x_105)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_105;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_104);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_unsigned_to_nat(1u);
x_124 = l_Lean_Syntax_getArg(x_1, x_123);
lean_dec(x_1);
x_125 = l_Lean_Syntax_getId(x_124);
x_126 = lean_box(0);
x_127 = lean_unbox(x_126);
x_128 = l_Lean_SourceInfo_fromRef(x_121, x_127);
lean_dec(x_121);
x_129 = lean_mk_string_unchecked("Lean", 4, 4);
x_130 = lean_mk_string_unchecked("Parser", 6, 6);
x_131 = lean_mk_string_unchecked("Term", 4, 4);
x_132 = lean_mk_string_unchecked("app", 3, 3);
x_133 = l_Lean_Name_mkStr4(x_129, x_130, x_131, x_132);
x_134 = lean_mk_string_unchecked("BuildKey.module", 15, 15);
x_135 = l_String_toSubstring_x27(x_134);
x_136 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_137 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_137);
lean_inc(x_136);
x_138 = l_Lean_Name_mkStr2(x_136, x_137);
lean_inc(x_27);
lean_inc(x_26);
x_139 = l_Lean_addMacroScope(x_26, x_138, x_27);
lean_inc(x_4);
x_140 = l_Lean_Name_mkStr3(x_4, x_136, x_137);
x_141 = lean_box(0);
lean_inc(x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_140);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_17);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_128);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_128);
lean_ctor_set(x_146, 1, x_135);
lean_ctor_set(x_146, 2, x_139);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_mk_string_unchecked("null", 4, 4);
x_148 = l_Lean_Name_mkStr1(x_147);
x_149 = lean_unbox(x_126);
x_150 = l_Lake_Name_quoteFrom(x_124, x_125, x_149);
lean_inc(x_148);
lean_inc(x_128);
x_151 = l_Lean_Syntax_node1(x_128, x_148, x_150);
lean_inc(x_133);
x_152 = l_Lean_Syntax_node2(x_128, x_133, x_146, x_151);
lean_inc(x_30);
x_153 = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(x_152, x_21, x_30, x_122);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_30, x_30, x_155);
lean_dec(x_30);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_unbox(x_126);
x_162 = l_Lean_SourceInfo_fromRef(x_158, x_161);
lean_dec(x_158);
x_163 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_164 = l_String_toSubstring_x27(x_163);
x_165 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_166 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_166);
lean_inc(x_165);
x_167 = l_Lean_Name_mkStr2(x_165, x_166);
x_168 = l_Lean_addMacroScope(x_26, x_167, x_27);
x_169 = l_Lean_Name_mkStr3(x_4, x_165, x_166);
if (lean_is_scalar(x_156)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_156;
 lean_ctor_set_tag(x_170, 1);
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_141);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_143);
lean_inc(x_162);
x_172 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_164);
lean_ctor_set(x_172, 2, x_168);
lean_ctor_set(x_172, 3, x_171);
lean_inc(x_162);
x_173 = l_Lean_Syntax_node1(x_162, x_148, x_154);
x_174 = l_Lean_Syntax_node2(x_162, x_133, x_172, x_173);
if (lean_is_scalar(x_160)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_160;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_159);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_176 = lean_ctor_get(x_17, 0);
lean_inc(x_176);
lean_dec(x_17);
x_177 = l_Lean_Syntax_getArg(x_1, x_15);
x_178 = lean_ctor_get(x_2, 5);
lean_inc(x_178);
x_179 = l_Lean_replaceRef(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
x_180 = lean_ctor_get(x_2, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_2, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_2, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 4);
lean_inc(x_184);
lean_dec(x_2);
lean_inc(x_182);
lean_inc(x_181);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_180);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_183);
lean_ctor_set(x_185, 4, x_184);
lean_ctor_set(x_185, 5, x_179);
x_186 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_185, x_185, x_3);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = lean_unsigned_to_nat(1u);
x_191 = l_Lean_Syntax_getArg(x_1, x_190);
lean_dec(x_1);
x_192 = l_Lean_Syntax_getId(x_191);
x_193 = lean_box(0);
x_194 = lean_unbox(x_193);
x_195 = l_Lean_SourceInfo_fromRef(x_187, x_194);
lean_dec(x_187);
x_196 = lean_mk_string_unchecked("Lean", 4, 4);
x_197 = lean_mk_string_unchecked("Parser", 6, 6);
x_198 = lean_mk_string_unchecked("Term", 4, 4);
x_199 = lean_mk_string_unchecked("app", 3, 3);
x_200 = l_Lean_Name_mkStr4(x_196, x_197, x_198, x_199);
x_201 = lean_mk_string_unchecked("BuildKey.module", 15, 15);
x_202 = l_String_toSubstring_x27(x_201);
x_203 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_204 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_204);
lean_inc(x_203);
x_205 = l_Lean_Name_mkStr2(x_203, x_204);
lean_inc(x_182);
lean_inc(x_181);
x_206 = l_Lean_addMacroScope(x_181, x_205, x_182);
lean_inc(x_4);
x_207 = l_Lean_Name_mkStr3(x_4, x_203, x_204);
x_208 = lean_box(0);
lean_inc(x_207);
if (lean_is_scalar(x_189)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_189;
 lean_ctor_set_tag(x_209, 1);
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_207);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
lean_inc(x_195);
x_214 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_214, 0, x_195);
lean_ctor_set(x_214, 1, x_202);
lean_ctor_set(x_214, 2, x_206);
lean_ctor_set(x_214, 3, x_213);
x_215 = lean_mk_string_unchecked("null", 4, 4);
x_216 = l_Lean_Name_mkStr1(x_215);
x_217 = lean_unbox(x_193);
x_218 = l_Lake_Name_quoteFrom(x_191, x_192, x_217);
lean_inc(x_216);
lean_inc(x_195);
x_219 = l_Lean_Syntax_node1(x_195, x_216, x_218);
lean_inc(x_200);
x_220 = l_Lean_Syntax_node2(x_195, x_200, x_214, x_219);
lean_inc(x_185);
x_221 = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(x_220, x_176, x_185, x_188);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_185, x_185, x_223);
lean_dec(x_185);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_unbox(x_193);
x_230 = l_Lean_SourceInfo_fromRef(x_226, x_229);
lean_dec(x_226);
x_231 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_232 = l_String_toSubstring_x27(x_231);
x_233 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_234 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_234);
lean_inc(x_233);
x_235 = l_Lean_Name_mkStr2(x_233, x_234);
x_236 = l_Lean_addMacroScope(x_181, x_235, x_182);
x_237 = l_Lean_Name_mkStr3(x_4, x_233, x_234);
if (lean_is_scalar(x_224)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_224;
 lean_ctor_set_tag(x_238, 1);
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_208);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_211);
lean_inc(x_230);
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_230);
lean_ctor_set(x_240, 1, x_232);
lean_ctor_set(x_240, 2, x_236);
lean_ctor_set(x_240, 3, x_239);
lean_inc(x_230);
x_241 = l_Lean_Syntax_node1(x_230, x_216, x_222);
x_242 = l_Lean_Syntax_node2(x_230, x_200, x_240, x_241);
if (lean_is_scalar(x_228)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_228;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_227);
return x_243;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x40_______x2f__________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_119 = lean_mk_string_unchecked("DSL", 3, 3);
x_120 = lean_mk_string_unchecked("term`@___/____", 14, 14);
lean_inc(x_4);
x_121 = l_Lean_Name_mkStr3(x_4, x_119, x_120);
lean_inc(x_1);
x_122 = l_Lean_Syntax_isOfKind(x_1, x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_box(1);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_unsigned_to_nat(1u);
x_127 = l_Lean_Syntax_getArg(x_1, x_126);
x_153 = lean_unsigned_to_nat(2u);
x_154 = l_Lean_Syntax_getArg(x_1, x_153);
x_155 = l_Lean_Syntax_isNone(x_154);
if (x_155 == 0)
{
uint8_t x_156; 
lean_inc(x_154);
x_156 = l_Lean_Syntax_matchesNull(x_154, x_153);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
lean_dec(x_127);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_box(1);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_3);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Lean_Syntax_getArg(x_154, x_126);
lean_dec(x_154);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_128 = x_160;
x_129 = x_2;
x_130 = x_3;
goto block_152;
}
}
else
{
lean_object* x_161; 
lean_dec(x_154);
x_161 = lean_box(0);
x_128 = x_161;
x_129 = x_2;
x_130 = x_3;
goto block_152;
}
block_152:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_131 = lean_unsigned_to_nat(3u);
x_132 = l_Lean_Syntax_getArg(x_1, x_131);
x_133 = l_Lean_Syntax_getArgs(x_132);
lean_dec(x_132);
x_134 = lean_array_size(x_133);
x_135 = lean_usize_of_nat(x_125);
x_136 = l_Array_mapMUnsafe_map___at___Lake_DSL___aux__Lake__DSL__Key______macroRules__Lake__DSL__term_x60_x2b________1_spec__0(x_134, x_135, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_4);
lean_dec(x_1);
x_137 = lean_box(1);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Syntax_getOptional_x3f(x_127);
lean_dec(x_127);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_141 = l_Lean_Syntax_getArg(x_1, x_125);
lean_dec(x_1);
x_142 = lean_box(0);
x_143 = lean_box(0);
x_144 = lean_unbox(x_143);
lean_inc(x_141);
x_145 = l_Lake_Name_quoteFrom(x_141, x_142, x_144);
x_70 = x_139;
x_71 = x_130;
x_72 = x_128;
x_73 = x_129;
x_74 = x_141;
x_75 = x_145;
goto block_118;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
lean_dec(x_140);
x_147 = l_Lean_Syntax_getArg(x_1, x_125);
lean_dec(x_1);
x_148 = l_Lean_Syntax_getId(x_146);
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_151 = l_Lake_Name_quoteFrom(x_146, x_148, x_150);
x_70 = x_139;
x_71 = x_130;
x_72 = x_128;
x_73 = x_129;
x_74 = x_147;
x_75 = x_151;
goto block_118;
}
}
}
}
block_69:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_7);
x_9 = l___private_Lake_DSL_Key_0__Lake_DSL_expandFacets(x_6, x_5, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_7, 5);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
lean_dec(x_12);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("app", 3, 3);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
x_23 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_24 = l_String_toSubstring_x27(x_23);
x_25 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_26 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_addMacroScope(x_17, x_27, x_16);
x_29 = l_Lean_Name_mkStr3(x_4, x_25, x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_15);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_15);
x_37 = l_Lean_Syntax_node1(x_15, x_36, x_11);
x_38 = l_Lean_Syntax_node2(x_15, x_22, x_34, x_37);
lean_ctor_set(x_9, 0, x_38);
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_ctor_get(x_7, 5);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_SourceInfo_fromRef(x_41, x_43);
lean_dec(x_41);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Term", 4, 4);
x_50 = lean_mk_string_unchecked("app", 3, 3);
x_51 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_50);
x_52 = lean_mk_string_unchecked("PartialBuildKey.mk", 18, 18);
x_53 = l_String_toSubstring_x27(x_52);
x_54 = lean_mk_string_unchecked("PartialBuildKey", 15, 15);
x_55 = lean_mk_string_unchecked("mk", 2, 2);
lean_inc(x_55);
lean_inc(x_54);
x_56 = l_Lean_Name_mkStr2(x_54, x_55);
x_57 = l_Lean_addMacroScope(x_46, x_56, x_45);
x_58 = l_Lean_Name_mkStr3(x_4, x_54, x_55);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_44);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_57);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
lean_inc(x_44);
x_66 = l_Lean_Syntax_node1(x_44, x_65, x_39);
x_67 = l_Lean_Syntax_node2(x_44, x_51, x_63, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_40);
return x_68;
}
}
block_118:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_73, 5);
lean_inc(x_76);
x_77 = l_Lean_replaceRef(x_74, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 4);
lean_inc(x_82);
lean_dec(x_73);
lean_inc(x_77);
lean_inc(x_80);
lean_inc(x_79);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set(x_83, 5, x_77);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_84 = lean_box(0);
x_85 = lean_unbox(x_84);
x_86 = l_Lean_SourceInfo_fromRef(x_77, x_85);
lean_dec(x_77);
x_87 = lean_mk_string_unchecked("Lean", 4, 4);
x_88 = lean_mk_string_unchecked("Parser", 6, 6);
x_89 = lean_mk_string_unchecked("Term", 4, 4);
x_90 = lean_mk_string_unchecked("app", 3, 3);
x_91 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_90);
x_92 = lean_mk_string_unchecked("BuildKey.package", 16, 16);
x_93 = l_String_toSubstring_x27(x_92);
x_94 = lean_mk_string_unchecked("BuildKey", 8, 8);
x_95 = lean_mk_string_unchecked("package", 7, 7);
lean_inc(x_95);
lean_inc(x_94);
x_96 = l_Lean_Name_mkStr2(x_94, x_95);
x_97 = l_Lean_addMacroScope(x_79, x_96, x_80);
lean_inc(x_4);
x_98 = l_Lean_Name_mkStr3(x_4, x_94, x_95);
x_99 = lean_box(0);
lean_inc(x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_98);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_86);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_93);
lean_ctor_set(x_105, 2, x_97);
lean_ctor_set(x_105, 3, x_104);
x_106 = lean_mk_string_unchecked("null", 4, 4);
x_107 = l_Lean_Name_mkStr1(x_106);
lean_inc(x_86);
x_108 = l_Lean_Syntax_node1(x_86, x_107, x_75);
x_109 = l_Lean_Syntax_node2(x_86, x_91, x_105, x_108);
x_5 = x_70;
x_6 = x_109;
x_7 = x_83;
x_8 = x_71;
goto block_69;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
x_110 = lean_ctor_get(x_72, 0);
lean_inc(x_110);
lean_dec(x_72);
x_111 = l___private_Lake_DSL_Key_0__Lake_DSL_expandPackageTargetLit(x_75, x_110, x_83, x_71);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_5 = x_70;
x_6 = x_112;
x_7 = x_83;
x_8 = x_113;
goto block_69;
}
else
{
uint8_t x_114; 
lean_dec(x_83);
lean_dec(x_70);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_111, 0);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_111);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Key(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
