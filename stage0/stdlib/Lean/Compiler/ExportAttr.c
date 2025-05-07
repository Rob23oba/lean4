// Lean compiler output
// Module: Lean.Compiler.ExportAttr
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
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exportAttr;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_15; uint8_t x_23; lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_8 = lean_string_utf8_get(x_1, x_3);
x_31 = lean_unsigned_to_nat(65u);
x_32 = lean_uint32_of_nat(x_31);
x_33 = lean_uint32_dec_le(x_32, x_8);
if (x_33 == 0)
{
x_23 = x_33;
goto block_30;
}
else
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(90u);
x_35 = lean_uint32_of_nat(x_34);
x_36 = lean_uint32_dec_le(x_8, x_35);
x_23 = x_36;
goto block_30;
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(95u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_8, x_12);
if (x_13 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
goto block_6;
}
}
else
{
if (x_9 == 0)
{
goto block_6;
}
else
{
lean_dec(x_3);
return x_9;
}
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_uint32_of_nat(x_16);
x_18 = lean_uint32_dec_le(x_17, x_8);
if (x_18 == 0)
{
x_9 = x_15;
x_10 = x_18;
goto block_14;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(57u);
x_20 = lean_uint32_of_nat(x_19);
x_21 = lean_uint32_dec_le(x_8, x_20);
x_9 = x_15;
x_10 = x_21;
goto block_14;
}
}
else
{
goto block_6;
}
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(97u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_uint32_dec_le(x_25, x_8);
if (x_26 == 0)
{
x_15 = x_26;
goto block_22;
}
else
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(122u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_uint32_dec_le(x_8, x_28);
x_15 = x_29;
goto block_22;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(lean_object* x_1) {
_start:
{
uint8_t x_13; lean_object* x_15; uint8_t x_16; lean_object* x_25; uint32_t x_26; uint32_t x_27; uint8_t x_28; 
x_15 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(65u);
x_26 = lean_uint32_of_nat(x_25);
x_27 = lean_string_utf8_get(x_1, x_15);
x_28 = lean_uint32_dec_le(x_26, x_27);
if (x_28 == 0)
{
x_16 = x_28;
goto block_24;
}
else
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(90u);
x_30 = lean_uint32_of_nat(x_29);
x_31 = lean_uint32_dec_le(x_27, x_30);
x_16 = x_31;
goto block_24;
}
block_12:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
x_6 = l_Substring_nextn(x_5, x_4, x_2);
lean_dec(x_5);
x_7 = l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(x_1, x_3, x_6);
lean_dec(x_3);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
block_14:
{
if (x_13 == 0)
{
lean_dec(x_1);
return x_13;
}
else
{
goto block_12;
}
}
block_24:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(97u);
x_18 = lean_uint32_of_nat(x_17);
x_19 = lean_string_utf8_get(x_1, x_15);
x_20 = lean_uint32_dec_le(x_18, x_19);
if (x_20 == 0)
{
x_13 = x_20;
goto block_14;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(122u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_dec_le(x_19, x_22);
x_13 = x_23;
goto block_14;
}
}
else
{
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at_____private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(x_3);
if (lean_obj_tag(x_2) == 0)
{
return x_4;
}
else
{
if (x_4 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
x_1 = x_2;
goto _start;
}
}
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("invalid 'export' function name, is not a valid C++ identifier", 61, 61);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_11, x_3, x_4, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_8);
return x_6;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94____boxed), 5, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94____boxed), 5, 0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("exportAttr", 10, 10);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_mk_string_unchecked("export", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("name to be used by code generators", 34, 34);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_2);
x_15 = l_Lean_registerParametricAttribute(lean_box(0), x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__0____x40_Lean_Compiler_ExportAttr___hyg_94_(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__1____x40_Lean_Compiler_ExportAttr___hyg_94_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__2____x40_Lean_Compiler_ExportAttr___hyg_94_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_get_export_name_for(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_exportAttr;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_isExport(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_get_export_name_for(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("main", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_name_eq(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExport___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExport(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ExportAttr___hyg_94_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_exportAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exportAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
