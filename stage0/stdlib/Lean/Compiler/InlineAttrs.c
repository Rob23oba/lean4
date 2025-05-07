// Lean compiler output
// Module: Lean.Compiler.InlineAttrs
// Imports: Lean.Attributes
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineIfReduceAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_setInlineAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_inline_attribute(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_inline_if_reduce_attribute(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
lean_object* l_Lean_EnumAttributes_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_inlineAttrs;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t lean_has_noinline_attribute(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_instInhabitedInlineAttributeKind;
LEAN_EXPORT lean_object* l_Lean_Compiler_hasMacroInlineAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineAttributeOld___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_macro_inline_attribute(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoInlineAttributeOld___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineIfReduceAttributeOld___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoInlineAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasAlwaysInlineAttribute(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18_(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instHashableInlineAttributeKind;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqInlineAttributeKind;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasMacroInlineAttributeOld___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasAlwaysInlineAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_InlineAttrs___hyg_267_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_setInlineAttribute(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInlineIfReduceAttribute(lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNoInlineAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36____boxed(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInlineAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_InlineAttributeKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Compiler_InlineAttributeKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InlineAttributeKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Compiler_InlineAttributeKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedInlineAttributeKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_InlineAttributeKind_toCtorIdx(x_1);
x_4 = l_Lean_Compiler_InlineAttributeKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_instBEqInlineAttributeKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_uint64_of_nat(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint64_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_uint64_of_nat(x_6);
return x_7;
}
case 3:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_uint64_of_nat(x_8);
return x_9;
}
default: 
{
lean_object* x_10; uint64_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_uint64_of_nat(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_instHashableInlineAttributeKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_21 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_20, x_2, x_3, x_8);
return x_21;
}
else
{
lean_object* x_22; 
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
x_37 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_36, x_2, x_3, x_24);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isConst(x_3);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_5 = l_Lean_Expr_constName_x21(x_3);
lean_inc(x_5);
x_12 = l_Lean_isBRecOnRecursor(x_2, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_mk_string_unchecked("WellFounded", 11, 11);
x_14 = lean_mk_string_unchecked("fix", 3, 3);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = lean_name_eq(x_5, x_15);
lean_dec(x_15);
x_6 = x_16;
goto block_11;
}
else
{
x_6 = x_12;
goto block_11;
}
block_11:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("_unary", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Name_append(x_1, x_8);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
x_12 = l_List_lengthTR(lean_box(0), x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = lean_box(x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_5);
x_16 = lean_st_ref_get(x_3, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_find_expr(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(x_14);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; 
lean_dec(x_22);
x_24 = lean_box(0);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0___boxed), 3, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_find_expr(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
x_38 = l_List_lengthTR(lean_box(0), x_37);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_1);
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_st_ref_get(x_3, x_35);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0___boxed), 3, 2);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_47);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_dec(x_36);
x_50 = lean_find_expr(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(x_40);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
x_53 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_5);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_5, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_dec(x_5);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
return x_5;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_5, 0);
x_63 = lean_ctor_get(x_5, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_5);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267_(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Compiler_checkIsDefinition(x_10, x_1);
x_12 = l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(x_11, x_3, x_4, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(x_2);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(x_1, x_3, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_mk_string_unchecked("invalid use of `[macro_inline]` attribute at `", 46, 46);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_20);
x_22 = lean_mk_string_unchecked("`, it is not supported in this kind of declaration, declaration must be a non-recursive definition", 98, 98);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_24, x_3, x_4, x_18);
return x_25;
}
else
{
uint8_t x_26; 
lean_free_object(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_15, 0, x_28);
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_free_object(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_12, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_free_object(x_6);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_1);
x_45 = l_Lean_Compiler_checkIsDefinition(x_44, x_1);
x_46 = l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(x_45, x_3, x_4, x_43);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_box(x_2);
if (lean_obj_tag(x_47) == 2)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_1);
x_49 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(x_1, x_3, x_4, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_mk_string_unchecked("invalid use of `[macro_inline]` attribute at `", 46, 46);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = l_Lean_MessageData_ofName(x_1);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("`, it is not supported in this kind of declaration, declaration must be a non-recursive definition", 98, 98);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_59, x_3, x_4, x_52);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_62 = x_49;
} else {
 lean_dec_ref(x_49);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_67 = x_49;
} else {
 lean_dec_ref(x_49);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_47);
lean_dec(x_1);
x_69 = lean_ctor_get(x_46, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_70 = x_46;
} else {
 lean_dec_ref(x_46);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_dec(x_1);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_InlineAttrs___hyg_267_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267____boxed), 5, 0);
x_3 = lean_mk_string_unchecked("inline", 6, 6);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("mark definition to be inlined", 29, 29);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("inline_if_reduce", 16, 16);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("mark definition to be inlined when resultant term after reduction is not a `cases_on` application", 97, 97);
x_12 = lean_box(3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("noinline", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("mark definition to never be inlined", 35, 35);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("macro_inline", 12, 12);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("mark definition to always be inlined before ANF conversion", 58, 58);
x_24 = lean_box(2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("always_inline", 13, 13);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_mk_string_unchecked("mark definition to be always inlined", 36, 36);
x_30 = lean_box(4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_box(0);
x_40 = lean_mk_string_unchecked("Lean", 4, 4);
x_41 = lean_mk_string_unchecked("Compiler", 8, 8);
x_42 = lean_mk_string_unchecked("inlineAttrs", 11, 11);
x_43 = l_Lean_Name_mkStr3(x_40, x_41, x_42);
x_44 = lean_unbox(x_39);
x_45 = l_Lean_registerEnumAttributes___redArg(x_38, x_2, x_44, x_43, x_1);
return x_45;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_InlineAttrs___hyg_267_(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_setInlineAttribute(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_inlineAttrs;
x_5 = lean_box(x_3);
x_6 = l_Lean_EnumAttributes_setValue___redArg(x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_setInlineAttribute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Compiler_setInlineAttribute(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_inlineAttrs;
x_5 = l_Lean_EnumAttributes_getValue(lean_box(0), x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_Compiler_inlineAttrs;
x_6 = l_Lean_EnumAttributes_getValue(lean_box(0), x_4, x_5, x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18_(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInlineAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasInlineAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInlineIfReduceAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(3);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineIfReduceAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasInlineIfReduceAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNoInlineAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoInlineAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasNoInlineAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasMacroInlineAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasMacroInlineAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasAlwaysInlineAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(4);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasAlwaysInlineAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasAlwaysInlineAttribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
x_4 = lean_is_eager_lambda_lifting_name(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Lean_Compiler_inlineAttrs;
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_EnumAttributes_getValue(lean_box(0), x_5, x_6, x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Name_isInternal(x_3);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_beqInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_18_(x_2, x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lean_has_inline_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineAttributeOld___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_inline_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_has_inline_if_reduce_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(3);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInlineIfReduceAttributeOld___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_inline_if_reduce_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_has_noinline_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoInlineAttributeOld___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_noinline_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_has_macro_inline_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasMacroInlineAttributeOld___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_macro_inline_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_instInhabitedInlineAttributeKind = _init_l_Lean_Compiler_instInhabitedInlineAttributeKind();
l_Lean_Compiler_instBEqInlineAttributeKind = _init_l_Lean_Compiler_instBEqInlineAttributeKind();
lean_mark_persistent(l_Lean_Compiler_instBEqInlineAttributeKind);
l_Lean_Compiler_instHashableInlineAttributeKind = _init_l_Lean_Compiler_instHashableInlineAttributeKind();
lean_mark_persistent(l_Lean_Compiler_instHashableInlineAttributeKind);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_InlineAttrs___hyg_267_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_inlineAttrs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_inlineAttrs);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
