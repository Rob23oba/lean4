// Lean compiler output
// Module: Lake.Config.Glob
// Imports: Lean.Util.Path Lake.Util.Name
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNameGlob___lam__0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprGlob;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeGlobArray;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNameGlob;
lean_object* l_Array_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_toString(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_term_____x2e_x2a;
LEAN_EXPORT lean_object* l_Lake_Glob_instToString;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqGlob(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_term_____x2e_x2b;
LEAN_EXPORT lean_object* l_Lake_Glob_matches___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Glob_toString___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Glob_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_toString___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedGlob;
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51____boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedGlob() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_to_int(x_21);
x_5 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_to_int(x_23);
x_5 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lake.Glob.one", 13, 13);
if (lean_is_scalar(x_4)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_4;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Name_reprPrec(x_3, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_26 = x_1;
} else {
 lean_dec_ref(x_1);
 x_26 = lean_box(0);
}
x_41 = lean_unsigned_to_nat(1024u);
x_42 = lean_nat_dec_le(x_41, x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_to_int(x_43);
x_27 = x_44;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_to_int(x_45);
x_27 = x_46;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_28 = lean_mk_string_unchecked("Lake.Glob.submodules", 20, 20);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(3, 1, 0);
} else {
 x_29 = x_26;
 lean_ctor_set_tag(x_29, 3);
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(1024u);
x_33 = l_Lean_Name_reprPrec(x_25, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = l_Repr_addAppParen(x_37, x_2);
return x_39;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_63; uint8_t x_64; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_48 = x_1;
} else {
 lean_dec_ref(x_1);
 x_48 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(1024u);
x_64 = lean_nat_dec_le(x_63, x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_to_int(x_65);
x_49 = x_66;
goto block_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_to_int(x_67);
x_49 = x_68;
goto block_62;
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_50 = lean_mk_string_unchecked("Lake.Glob.andSubmodules", 23, 23);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(3, 1, 0);
} else {
 x_51 = x_48;
 lean_ctor_set_tag(x_51, 3);
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_box(1);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(1024u);
x_55 = l_Lean_Name_reprPrec(x_47, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = l_Repr_addAppParen(x_59, x_2);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprGlob() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_Glob_0__Lake_reprGlob____x40_Lake_Config_Glob___hyg_51____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_name_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_3);
return x_7;
}
else
{
return x_6;
}
}
else
{
uint8_t x_8; 
x_8 = lean_unbox(x_3);
return x_8;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_unbox(x_3);
return x_12;
}
else
{
return x_11;
}
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_3);
return x_13;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_name_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_3);
return x_17;
}
else
{
return x_16;
}
}
else
{
uint8_t x_18; 
x_18 = lean_unbox(x_3);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqGlob(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lake_Config_Glob_0__Lake_decEqGlob____x40_Lake_Config_Glob___hyg_197_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqGlob(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeNameGlob___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeNameGlob() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeNameGlob___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeGlobArray() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_singleton), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_term_____x2e_x2a() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("term__.*", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("name", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("group", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("noWs", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked(".*", 2, 2);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_5 = lean_mk_string_unchecked("term__.*", 8, 8);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_20);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Name_mkStr4(x_12, x_13, x_20, x_21);
x_23 = lean_mk_string_unchecked("Glob.andSubmodules", 18, 18);
x_24 = l_String_toSubstring_x27(x_23);
x_25 = lean_mk_string_unchecked("Glob", 4, 4);
x_26 = lean_mk_string_unchecked("andSubmodules", 13, 13);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_addMacroScope(x_19, x_27, x_18);
x_29 = l_Lean_Name_mkStr3(x_4, x_25, x_26);
x_30 = lean_box(0);
lean_inc(x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_17);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_mk_string_unchecked("null", 4, 4);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_mk_string_unchecked("quotedName", 10, 10);
x_40 = l_Lean_Name_mkStr4(x_12, x_13, x_20, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
x_43 = lean_array_push(x_42, x_11);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_43);
lean_inc(x_17);
x_46 = l_Lean_Syntax_node1(x_17, x_38, x_45);
x_47 = l_Lean_Syntax_node2(x_17, x_22, x_36, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
}
}
static lean_object* _init_l_Lake_term_____x2e_x2b() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("term__.+", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("name", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("group", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("noWs", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked(".+", 2, 2);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_5 = lean_mk_string_unchecked("term__.+", 8, 8);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("Term", 4, 4);
x_21 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_20);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Name_mkStr4(x_12, x_13, x_20, x_21);
x_23 = lean_mk_string_unchecked("Glob.submodules", 15, 15);
x_24 = l_String_toSubstring_x27(x_23);
x_25 = lean_mk_string_unchecked("Glob", 4, 4);
x_26 = lean_mk_string_unchecked("submodules", 10, 10);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_addMacroScope(x_19, x_27, x_18);
x_29 = l_Lean_Name_mkStr3(x_4, x_25, x_26);
x_30 = lean_box(0);
lean_inc(x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_17);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_mk_string_unchecked("null", 4, 4);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_mk_string_unchecked("quotedName", 10, 10);
x_40 = l_Lean_Name_mkStr4(x_12, x_13, x_20, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
x_43 = lean_array_push(x_42, x_11);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_43);
lean_inc(x_17);
x_46 = l_Lean_Syntax_node1(x_17, x_38, x_45);
x_47 = l_Lean_Syntax_node2(x_17, x_22, x_36, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Glob_toString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_Glob_toString___lam__0___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_2, x_5, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_Glob_toString___lam__0___boxed), 1, 0);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_7, x_10, x_8);
x_12 = lean_mk_string_unchecked(".+", 2, 2);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l_Lake_Glob_toString___lam__0___boxed), 1, 0);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Name_toString(x_14, x_17, x_15);
x_19 = lean_mk_string_unchecked(".*", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_toString___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Glob_toString___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Glob_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Glob_toString), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Glob_matches(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
case 1:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_Name_isPrefixOf(x_5, x_1);
if (x_6 == 0)
{
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_name_eq(x_5, x_1);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
default: 
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_Name_isPrefixOf(x_10, x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_matches___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Glob_matches(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Name_append(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = l_Lean_modToFilePath(x_1, x_2, x_7);
lean_dec(x_7);
x_9 = l_Lean_forEachModuleInDir___redArg(x_3, x_4, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_4);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = l_Lean_modToFilePath(x_3, x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_12 = l_Lean_forEachModuleInDir___redArg(x_1, x_2, x_11, x_9);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_4);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_1(x_4, x_15);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_5, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_5);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_modToFilePath(x_4, x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_13 = l_Lean_forEachModuleInDir___redArg(x_2, x_3, x_12, x_10);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_5);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_17);
x_19 = lean_apply_1(x_5, x_16);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Glob_forEachModuleIn___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Glob(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedGlob = _init_l_Lake_instInhabitedGlob();
lean_mark_persistent(l_Lake_instInhabitedGlob);
l_Lake_instReprGlob = _init_l_Lake_instReprGlob();
lean_mark_persistent(l_Lake_instReprGlob);
l_Lake_instCoeNameGlob = _init_l_Lake_instCoeNameGlob();
lean_mark_persistent(l_Lake_instCoeNameGlob);
l_Lake_instCoeGlobArray = _init_l_Lake_instCoeGlobArray();
lean_mark_persistent(l_Lake_instCoeGlobArray);
l_Lake_term_____x2e_x2a = _init_l_Lake_term_____x2e_x2a();
lean_mark_persistent(l_Lake_term_____x2e_x2a);
l_Lake_term_____x2e_x2b = _init_l_Lake_term_____x2e_x2b();
lean_mark_persistent(l_Lake_term_____x2e_x2b);
l_Lake_Glob_instToString = _init_l_Lake_Glob_instToString();
lean_mark_persistent(l_Lake_Glob_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
