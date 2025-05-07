// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: Init.Data.Repr Init.Data.Option.Basic
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
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_toInt_x21_spec__0(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt___lam__0(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
extern lean_object* l_Int_instInhabited;
lean_object* l_Substring_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt16;
LEAN_EXPORT lean_object* l_instToStringSubstring___lam__0(lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_instToStringNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringChar;
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringPos;
LEAN_EXPORT lean_object* l_instToStringList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___addParenHeuristic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt32;
LEAN_EXPORT lean_object* l_instToStringFin(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFormat;
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringPUnit;
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addParenHeuristic___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instToStringULift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringNat;
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt8;
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instToStringBool;
LEAN_EXPORT lean_object* l_instToStringFin___lam__0(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubstring;
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt64;
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___addParenHeuristic_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT uint8_t l_String_isInt(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubstring___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringIterator;
LEAN_EXPORT lean_object* l_instToStringUnit;
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUSize;
LEAN_EXPORT lean_object* l_instToStringInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringString;
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringPos___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringId(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId__1___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringId__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_instToStringString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringString___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringSubstring___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_instToStringSubstring() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringSubstring___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringSubstring___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringSubstring___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_instToStringIterator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringIterator___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("false", 5, 5);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("true", 4, 4);
return x_3;
}
}
}
static lean_object* _init_l_instToStringBool() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringBool___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringBool___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("false", 5, 5);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("true", 4, 4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringDecidable___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringDecidable___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked(", ", 2, 2);
x_5 = lean_string_append(x_2, x_4);
lean_dec(x_4);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_toString___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("[]", 2, 2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("]", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_toString___redArg___lam__0), 3, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_mk_string_unchecked("[", 1, 1);
x_14 = lean_apply_1(x_1, x_11);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_List_foldl___redArg(x_12, x_15, x_4);
x_17 = lean_unsigned_to_nat(93u);
x_18 = l_Char_ofNat(x_17);
x_19 = lean_string_push(x_16, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_toString___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_toString), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("()", 2, 2);
return x_2;
}
}
static lean_object* _init_l_instToStringPUnit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringPUnit___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringPUnit___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringULift___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUnit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringPUnit___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringNat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringPos___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringPos___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_1);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_nat_abs(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("-", 1, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
return x_14;
}
}
}
static lean_object* _init_l_instToStringInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringInt___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instToStringChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringChar___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringChar___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringFin___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt8___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt8___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt16___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt16___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt32___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt32___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUInt64___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt64___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringUSize() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringUSize___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instToStringUSize___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(120u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_instToStringFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringFormat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___addParenHeuristic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_dec(x_3);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_9 = lean_string_utf8_get(x_1, x_3);
x_18 = lean_unsigned_to_nat(32u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_9, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(9u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_9, x_22);
x_10 = x_23;
goto block_17;
}
else
{
x_10 = x_20;
goto block_17;
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(13u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(10u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_9, x_15);
x_4 = x_16;
goto block_7;
}
else
{
x_4 = x_13;
goto block_7;
}
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
block_7:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_15; 
x_2 = lean_mk_string_unchecked("(", 1, 1);
x_15 = l_String_isPrefixOf(x_2, x_1);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("[", 1, 1);
x_17 = l_String_isPrefixOf(x_16, x_1);
lean_dec(x_16);
x_3 = x_17;
goto block_14;
}
else
{
x_3 = x_15;
goto block_14;
}
block_14:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_mk_string_unchecked("{", 1, 1);
x_5 = l_String_isPrefixOf(x_4, x_1);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_mk_string_unchecked("#[", 2, 2);
x_7 = l_String_isPrefixOf(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_String_anyAux___at___addParenHeuristic_spec__0(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_append(x_2, x_1);
x_12 = lean_mk_string_unchecked(")", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
return x_13;
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___addParenHeuristic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___addParenHeuristic_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_addParenHeuristic(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("none", 4, 4);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_mk_string_unchecked("(some ", 6, 6);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_addParenHeuristic(x_6);
lean_dec(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked(")", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToStringOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("(inl ", 5, 5);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_addParenHeuristic(x_6);
lean_dec(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked(")", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_mk_string_unchecked("(inr ", 5, 5);
x_13 = lean_apply_1(x_2, x_11);
x_14 = l_addParenHeuristic(x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked(")", 1, 1);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instToStringSum___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("(", 1, 1);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked(", ", 2, 2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked(")", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instToStringProd___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("⟨", 3, 1);
lean_inc(x_4);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked(", ", 2, 2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_apply_2(x_2, x_4, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("⟩", 3, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instToStringSigma___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instToStringSubtype___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_unsigned_to_nat(45u);
x_5 = l_Char_ofNat(x_4);
x_6 = l_instDecidableEqChar(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_String_toNat_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_nat_to_int(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_string_utf8_byte_size(x_1);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_15);
x_18 = l_Substring_nextn(x_17, x_16, x_2);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_15);
x_20 = l_Substring_toNat_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_int_neg(x_24);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_nat_to_int(x_26);
x_28 = lean_int_neg(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_8 = l_instDecidableEqPos(x_5, x_6);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(48u);
x_14 = lean_uint32_of_nat(x_13);
x_15 = lean_string_utf8_get(x_2, x_4);
x_16 = lean_uint32_dec_le(x_14, x_15);
if (x_16 == 0)
{
x_9 = x_16;
goto block_12;
}
else
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(57u);
x_18 = lean_uint32_of_nat(x_17);
x_19 = lean_uint32_dec_le(x_15, x_18);
x_9 = x_19;
goto block_12;
}
block_12:
{
if (x_9 == 0)
{
lean_dec(x_4);
return x_7;
}
else
{
if (x_8 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Substring_nextn(x_7, x_8, x_6);
lean_dec(x_7);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_11 = lean_nat_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_12 = lean_nat_dec_eq(x_10, x_6);
lean_dec(x_10);
x_17 = lean_unsigned_to_nat(48u);
x_18 = lean_uint32_of_nat(x_17);
x_19 = lean_string_utf8_get(x_2, x_4);
x_20 = lean_uint32_dec_le(x_18, x_19);
if (x_20 == 0)
{
x_13 = x_20;
goto block_16;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(57u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_dec_le(x_19, x_22);
x_13 = x_23;
goto block_16;
}
block_16:
{
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
else
{
if (x_12 == 0)
{
lean_object* x_14; 
x_14 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_unsigned_to_nat(45u);
x_5 = l_Char_ofNat(x_4);
x_6 = l_instDecidableEqChar(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = l_instDecidableEqPos(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_String_anyAux___at___String_isInt_spec__0(x_1, x_1, x_7, x_2);
lean_dec(x_7);
lean_dec(x_1);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
return x_8;
}
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_string_utf8_byte_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_12);
x_15 = l_Substring_nextn(x_14, x_13, x_2);
lean_dec(x_14);
x_16 = lean_nat_sub(x_12, x_15);
x_17 = lean_nat_dec_eq(x_16, x_2);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_1);
x_18 = l_String_anyAux___at___String_isInt_spec__1(x_1, x_1, x_12, x_15);
lean_dec(x_12);
lean_dec(x_1);
if (x_18 == 0)
{
return x_6;
}
else
{
return x_17;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___String_isInt_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___String_isInt_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___String_toInt_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Int_instInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toInt_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("Int expected", 12, 12);
x_4 = l_panic___at___String_toInt_x21_spec__0(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("error: ", 7, 7);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_mk_string_unchecked("ok: ", 4, 4);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instToStringExcept___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_mk_string_unchecked("Except.error ", 13, 13);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = lean_apply_2(x_1, x_6, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Repr_addAppParen(x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_mk_string_unchecked("Except.error ", 13, 13);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_apply_2(x_1, x_12, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_4);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_mk_string_unchecked("Except.ok ", 10, 10);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_21);
x_22 = lean_unsigned_to_nat(1024u);
x_23 = lean_apply_2(x_2, x_20, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Repr_addAppParen(x_24, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_mk_string_unchecked("Except.ok ", 10, 10);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unsigned_to_nat(1024u);
x_30 = lean_apply_2(x_2, x_26, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Repr_addAppParen(x_31, x_4);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instReprExcept___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instReprExcept___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instToStringString = _init_l_instToStringString();
lean_mark_persistent(l_instToStringString);
l_instToStringSubstring = _init_l_instToStringSubstring();
lean_mark_persistent(l_instToStringSubstring);
l_instToStringIterator = _init_l_instToStringIterator();
lean_mark_persistent(l_instToStringIterator);
l_instToStringBool = _init_l_instToStringBool();
lean_mark_persistent(l_instToStringBool);
l_instToStringPUnit = _init_l_instToStringPUnit();
lean_mark_persistent(l_instToStringPUnit);
l_instToStringUnit = _init_l_instToStringUnit();
lean_mark_persistent(l_instToStringUnit);
l_instToStringNat = _init_l_instToStringNat();
lean_mark_persistent(l_instToStringNat);
l_instToStringPos = _init_l_instToStringPos();
lean_mark_persistent(l_instToStringPos);
l_instToStringInt = _init_l_instToStringInt();
lean_mark_persistent(l_instToStringInt);
l_instToStringChar = _init_l_instToStringChar();
lean_mark_persistent(l_instToStringChar);
l_instToStringUInt8 = _init_l_instToStringUInt8();
lean_mark_persistent(l_instToStringUInt8);
l_instToStringUInt16 = _init_l_instToStringUInt16();
lean_mark_persistent(l_instToStringUInt16);
l_instToStringUInt32 = _init_l_instToStringUInt32();
lean_mark_persistent(l_instToStringUInt32);
l_instToStringUInt64 = _init_l_instToStringUInt64();
lean_mark_persistent(l_instToStringUInt64);
l_instToStringUSize = _init_l_instToStringUSize();
lean_mark_persistent(l_instToStringUSize);
l_instToStringFormat = _init_l_instToStringFormat();
lean_mark_persistent(l_instToStringFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
