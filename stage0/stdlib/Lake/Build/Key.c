// Lean compiler output
// Module: Lake.Build.Key
// Imports: Lake.Util.Name Lake.Config.Kinds
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PartialBuildKey_toString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PartialBuildKey_toString___lam__2(uint8_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lake_PartialBuildKey_parse_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse_parseTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey_match__1_splitter____x40_Lake_Build_Key___hyg_69_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280_(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprPartialBuildKey;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringPartialBuildKey;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse_parsePackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_PartialBuildKey_parse_spec__0(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey;
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__1(lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBuildKey;
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object*);
LEAN_EXPORT uint64_t l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993_(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_instToString;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__0___boxed(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_moduleTargetIndicator;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey_match__1_splitter___redArg____x40_Lake_Build_Key___hyg_69_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedBuildKey() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_mk_string_unchecked("Lake.BuildKey.module", 20, 20);
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
x_28 = lean_mk_string_unchecked("Lake.BuildKey.package", 21, 21);
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
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_67; uint8_t x_68; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_49 = x_1;
} else {
 lean_dec_ref(x_1);
 x_49 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(1024u);
x_68 = lean_nat_dec_le(x_67, x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_to_int(x_69);
x_50 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_to_int(x_71);
x_50 = x_72;
goto block_66;
}
block_66:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_51 = lean_mk_string_unchecked("Lake.BuildKey.packageTarget", 27, 27);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_box(1);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(5, 2, 0);
} else {
 x_54 = x_49;
 lean_ctor_set_tag(x_54, 5);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_unsigned_to_nat(1024u);
x_56 = l_Lean_Name_reprPrec(x_47, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
x_59 = l_Lean_Name_reprPrec(x_48, x_55);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = l_Repr_addAppParen(x_63, x_2);
return x_65;
}
}
default: 
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_93; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_75 = x_1;
} else {
 lean_dec_ref(x_1);
 x_75 = lean_box(0);
}
x_76 = lean_unsigned_to_nat(1024u);
x_93 = lean_nat_dec_le(x_76, x_2);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_to_int(x_94);
x_77 = x_95;
goto block_92;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_to_int(x_96);
x_77 = x_97;
goto block_92;
}
block_92:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_78 = lean_mk_string_unchecked("Lake.BuildKey.facet", 19, 19);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_box(1);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(5, 2, 0);
} else {
 x_81 = x_75;
 lean_ctor_set_tag(x_81, 5);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(x_73, x_76);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = l_Lean_Name_reprPrec(x_74, x_76);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = l_Repr_addAppParen(x_89, x_2);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBuildKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280_(lean_object* x_1, lean_object* x_2) {
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
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_name_eq(x_14, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_unbox(x_3);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_name_eq(x_15, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = lean_unbox(x_3);
return x_21;
}
else
{
return x_20;
}
}
}
else
{
uint8_t x_22; 
x_22 = lean_unbox(x_3);
return x_22;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280_(x_23, x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_unbox(x_3);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_name_eq(x_24, x_26);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_unbox(x_3);
return x_30;
}
else
{
return x_29;
}
}
}
else
{
uint8_t x_31; 
x_31 = lean_unbox(x_3);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lake_Build_Key_0__Lake_decEqBuildKey____x40_Lake_Build_Key___hyg_280_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqBuildKey(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = l_Lean_Name_hash___override(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = l_Lean_Name_hash___override(x_12);
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = l_Lean_Name_hash___override(x_13);
x_19 = lean_uint64_mix_hash(x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993_(x_20);
x_25 = lean_uint64_mix_hash(x_23, x_24);
x_26 = l_Lean_Name_hash___override(x_21);
x_27 = lean_uint64_mix_hash(x_25, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashableBuildKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Key_0__Lake_hashBuildKey____x40_Lake_Build_Key___hyg_993____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_PartialBuildKey_moduleTargetIndicator() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("_+", 2, 2);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PartialBuildKey_mk(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_instDecidableEqPos(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Substring_nextn(x_7, x_8, x_4);
lean_dec(x_7);
lean_inc(x_9);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_string_utf8_byte_size(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Substring_beq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_14 = l_Lake_stringToLegalOrSimpleName(x_2);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_string_utf8_extract(x_2, x_9, x_3);
lean_dec(x_3);
lean_dec(x_9);
lean_dec(x_2);
x_18 = l_Lake_stringToLegalOrSimpleName(x_17);
x_19 = l_Lake_PartialBuildKey_moduleTargetIndicator;
x_20 = l_Lean_Name_append(x_18, x_19);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_mk_string_unchecked("ill-formed target: default package targets are not supported in partial build keys", 82, 82);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse_parseTarget(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_mk_string_unchecked("/", 1, 1);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_string_dec_eq(x_40, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_box(0);
x_45 = l_String_splitOnAux(x_1, x_40, x_43, x_43, x_43, x_44);
lean_dec(x_40);
lean_dec(x_1);
if (lean_obj_tag(x_45) == 0)
{
goto block_4;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_5 = x_47;
goto block_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_mk_string_unchecked("@", 1, 1);
x_60 = lean_string_utf8_byte_size(x_48);
lean_inc(x_60);
lean_inc(x_48);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_43);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Substring_nextn(x_61, x_62, x_43);
lean_dec(x_61);
lean_inc(x_63);
lean_inc(x_48);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_43);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_string_utf8_byte_size(x_59);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_43);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Substring_beq(x_64, x_66);
if (x_67 == 0)
{
lean_dec(x_63);
lean_dec(x_60);
x_51 = x_48;
goto block_58;
}
else
{
lean_object* x_68; 
x_68 = lean_string_utf8_extract(x_48, x_63, x_60);
lean_dec(x_60);
lean_dec(x_63);
lean_dec(x_48);
x_51 = x_68;
goto block_58;
}
}
else
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
goto block_4;
}
block_58:
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_string_utf8_byte_size(x_51);
x_53 = l_instDecidableEqPos(x_52, x_43);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lake_stringToLegalOrSimpleName(x_51);
x_55 = l_Lake_PartialBuildKey_parse_parsePackageTarget(x_54, x_49);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = l_Lake_PartialBuildKey_parse_parsePackageTarget(x_56, x_49);
return x_57;
}
}
}
}
}
else
{
lean_dec(x_40);
x_5 = x_1;
goto block_39;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("ill-formed target: too many '/'", 31, 31);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
block_39:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_instDecidableEqPos(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Substring_nextn(x_10, x_11, x_7);
lean_dec(x_10);
lean_inc(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_string_utf8_byte_size(x_9);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_14);
lean_inc(x_13);
x_16 = l_Substring_beq(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_mk_string_unchecked("+", 1, 1);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Substring_beq(x_13, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = l_Lake_PartialBuildKey_parse_parsePackageTarget(x_21, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_string_utf8_extract(x_5, x_12, x_6);
lean_dec(x_6);
lean_dec(x_12);
lean_dec(x_5);
x_24 = l_Lake_stringToLegalOrSimpleName(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_13);
x_27 = lean_string_utf8_extract(x_5, x_12, x_6);
lean_dec(x_6);
lean_dec(x_12);
lean_dec(x_5);
x_28 = lean_string_utf8_byte_size(x_27);
x_29 = l_instDecidableEqPos(x_28, x_7);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lake_stringToLegalOrSimpleName(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_5);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_PartialBuildKey_parse_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_instDecidableEqPos(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lake_stringToLegalOrSimpleName(x_5);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_1);
x_1 = x_2;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("ill-formed target: empty facet", 30, 30);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_instDecidableEqPos(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lake_stringToLegalOrSimpleName(x_14);
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_1 = x_20;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_22 = lean_mk_string_unchecked("ill-formed target: empty facet", 30, 30);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lake_PartialBuildKey_parse_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_panic_fn(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_instDecidableEqPos(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_mk_string_unchecked(":", 1, 1);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_String_splitOnAux(x_1, x_11, x_9, x_9, x_9, x_14);
lean_dec(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_mk_string_unchecked("Lake.Build.Key", 14, 14);
x_17 = lean_mk_string_unchecked("Lake.PartialBuildKey.parse", 26, 26);
x_18 = lean_unsigned_to_nat(54u);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_21 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_22 = l_panic___at___Lake_PartialBuildKey_parse_spec__1(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_2 = x_23;
x_3 = x_24;
goto block_7;
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = lean_box(0);
x_2 = x_1;
x_3 = x_25;
goto block_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_mk_string_unchecked("ill-formed target: empty string", 31, 31);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_7:
{
lean_object* x_4; 
x_4 = l_Lake_PartialBuildKey_parse_parseTarget(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_List_foldlM___at___Lake_PartialBuildKey_parse_spec__0(x_5, x_3);
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PartialBuildKey_toString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("+", 1, 1);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_2, x_5, x_1);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lake_PartialBuildKey_toString___lam__2(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_PartialBuildKey_toString___lam__1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_isAnonymous(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__2___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("@", 1, 1);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_5, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_mk_string_unchecked("", 0, 0);
return x_14;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_28 = l_Lake_PartialBuildKey_moduleTargetIndicator;
lean_inc(x_16);
x_29 = l_Lean_Name_eraseSuffix_x3f(x_16, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Name_toString(x_16, x_31, x_2);
x_17 = x_32;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lake_PartialBuildKey_toString___lam__1(x_2, x_33);
x_17 = x_34;
goto block_27;
}
block_27:
{
uint8_t x_18; 
x_18 = l_Lean_Name_isAnonymous(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__2___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_15, x_22, x_20);
x_24 = lean_mk_string_unchecked("/", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_17);
lean_dec(x_17);
return x_26;
}
else
{
lean_dec(x_15);
return x_17;
}
}
}
default: 
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Name_isAnonymous(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_box(x_37);
x_39 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__2___boxed), 2, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = l_Lake_PartialBuildKey_toString(x_35);
x_41 = lean_mk_string_unchecked(":", 1, 1);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = lean_box(1);
x_44 = lean_unbox(x_43);
x_45 = l_Lean_Name_toString(x_36, x_44, x_39);
x_46 = lean_string_append(x_42, x_45);
lean_dec(x_45);
return x_46;
}
else
{
lean_dec(x_36);
x_1 = x_35;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_PartialBuildKey_toString___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_PartialBuildKey_toString___lam__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instToStringPartialBuildKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprPartialBuildKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
x_4 = lean_mk_string_unchecked("+", 1, 1);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_2, x_6, x_3);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
x_11 = lean_mk_string_unchecked("@", 1, 1);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Name_toString(x_9, x_13, x_10);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
lean_inc(x_18);
x_21 = l_Lean_Name_toString(x_16, x_20, x_18);
x_22 = lean_mk_string_unchecked("/", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_unbox(x_19);
x_25 = l_Lean_Name_toString(x_17, x_24, x_18);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
x_30 = l_Lake_BuildKey_toString(x_27);
x_31 = lean_mk_string_unchecked(":", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l_Lake_Name_eraseHead(x_28);
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Name_toString(x_33, x_35, x_29);
x_37 = lean_string_append(x_32, x_36);
lean_dec(x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lake_PartialBuildKey_toString___lam__0___boxed), 1, 0);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_2);
x_12 = l_Lean_Name_toString(x_8, x_11, x_2);
x_13 = lean_mk_string_unchecked("/", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_unbox(x_10);
x_16 = l_Lean_Name_toString(x_9, x_15, x_2);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lake_BuildKey_toSimpleString(x_18);
x_21 = lean_mk_string_unchecked(":", 1, 1);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Lake_Name_eraseHead(x_19);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Name_toString(x_23, x_25, x_2);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
return x_27;
}
default: 
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_3 = x_28;
goto block_7;
}
}
block_7:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_3, x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildKey_toString(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildKey_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildKey_instToString___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickCmp(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(2);
x_9 = lean_unbox(x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_Name_quickCmp(x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_Name_quickCmp(x_15, x_17);
x_20 = lean_box(x_19);
if (lean_obj_tag(x_20) == 1)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickCmp(x_16, x_18);
return x_21;
}
else
{
lean_dec(x_20);
return x_19;
}
}
case 3:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
default: 
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(2);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = l_Lake_BuildKey_quickCmp(x_26, x_28);
x_31 = lean_box(x_30);
if (lean_obj_tag(x_31) == 1)
{
uint8_t x_32; 
x_32 = l_Lean_Name_quickCmp(x_27, x_29);
return x_32;
}
else
{
lean_dec(x_31);
return x_30;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(2);
x_34 = lean_unbox(x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_BuildKey_quickCmp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey_match__1_splitter___redArg____x40_Lake_Build_Key___hyg_69_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey_match__1_splitter____x40_Lake_Build_Key___hyg_69_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Key_0__Lake_reprBuildKey_match__1_splitter___redArg____x40_Lake_Build_Key___hyg_69_(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__2_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__2_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__5_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(x_1);
x_6 = lean_apply_2(x_3, x_5, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___redArg(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__3_splitter(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Kinds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Key(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Kinds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedBuildKey = _init_l_Lake_instInhabitedBuildKey();
lean_mark_persistent(l_Lake_instInhabitedBuildKey);
l_Lake_instReprBuildKey = _init_l_Lake_instReprBuildKey();
lean_mark_persistent(l_Lake_instReprBuildKey);
l_Lake_instHashableBuildKey = _init_l_Lake_instHashableBuildKey();
lean_mark_persistent(l_Lake_instHashableBuildKey);
l_Lake_PartialBuildKey_moduleTargetIndicator = _init_l_Lake_PartialBuildKey_moduleTargetIndicator();
lean_mark_persistent(l_Lake_PartialBuildKey_moduleTargetIndicator);
l_Lake_instToStringPartialBuildKey = _init_l_Lake_instToStringPartialBuildKey();
lean_mark_persistent(l_Lake_instToStringPartialBuildKey);
l_Lake_instReprPartialBuildKey = _init_l_Lake_instReprPartialBuildKey();
lean_mark_persistent(l_Lake_instReprPartialBuildKey);
l_Lake_BuildKey_instToString = _init_l_Lake_BuildKey_instToString();
lean_mark_persistent(l_Lake_BuildKey_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
