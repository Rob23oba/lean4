// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: Init.Data.List.BasicAux Lean.Expr Lean.Environment Lean.Attributes Lean.ProjFns Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry;
lean_object* l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData;
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed(lean_object*);
lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData;
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry;
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0(uint64_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_name_eq(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_3 = x_15;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
goto block_9;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_3 = x_21;
x_4 = x_22;
x_5 = x_23;
x_6 = x_24;
goto block_9;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
x_6 = x_30;
goto block_9;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
block_9:
{
uint8_t x_7; 
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(lean_object* x_1) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = l_Lean_Name_hash___override(x_7);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = lean_string_hash(x_8);
x_14 = lean_uint64_mix_hash(x_12, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = l_Lean_Name_hash___override(x_15);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_string_hash(x_16);
x_22 = lean_uint64_mix_hash(x_20, x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = l_Lean_Name_hash___override(x_23);
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_29 = lean_string_hash(x_24);
x_30 = lean_uint64_mix_hash(x_28, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_____private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382__spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_uint64_of_nat(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; uint64_t x_14; 
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_uint64_of_nat(x_13);
x_6 = x_14;
goto block_12;
}
else
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_unsigned_to_nat(13u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_mix_hash(x_16, x_18);
x_6 = x_19;
goto block_12;
}
block_12:
{
uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_unsigned_to_nat(7u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0(x_9, x_3);
x_11 = lean_uint64_mix_hash(x_7, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at_____private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456__spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_10 = lean_unsigned_to_nat(1u);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_array_uget(x_1, x_3);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Syntax_getArg(x_18, x_42);
x_44 = l_Lean_Syntax_isNone(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Syntax_getArg(x_43, x_42);
lean_dec(x_43);
x_46 = l_Lean_Syntax_getId(x_45);
lean_dec(x_45);
x_30 = x_46;
goto block_41;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
x_47 = lean_mk_string_unchecked("all", 3, 3);
x_48 = l_Lean_Name_mkStr1(x_47);
x_30 = x_48;
goto block_41;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = lean_usize_of_nat(x_10);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
block_29:
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Syntax_getArg(x_18, x_10);
lean_dec(x_18);
x_24 = l_Lean_Syntax_isNone(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_array_push(x_20, x_25);
x_11 = x_26;
x_12 = x_22;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_21);
x_28 = lean_array_push(x_20, x_27);
x_11 = x_28;
x_12 = x_22;
goto block_16;
}
}
block_41:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Syntax_getArg(x_18, x_17);
x_32 = l_Lean_Syntax_isStrLit_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_4);
x_33 = lean_mk_string_unchecked("string literal expected", 23, 23);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(x_31, x_34, x_5, x_6, x_7);
lean_dec(x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_19 = x_30;
x_20 = x_4;
x_21 = x_40;
x_22 = x_7;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_35; lean_object* x_45; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = l_Lean_Syntax_getArg(x_1, x_48);
x_50 = l_Lean_Syntax_isNone(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_49, x_51);
lean_dec(x_49);
x_53 = l_Lean_Syntax_isNatLit_x3f(x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
x_45 = x_51;
goto block_47;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_45 = x_54;
goto block_47;
}
}
else
{
lean_object* x_55; 
lean_dec(x_49);
x_55 = lean_box(0);
x_35 = x_55;
goto block_44;
}
block_34:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_size(x_6);
x_11 = lean_usize_of_nat(x_8);
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(x_6, x_10, x_11, x_9, x_2, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_to_list(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_array_to_list(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_box(0);
x_27 = lean_mk_string_unchecked("all", 3, 3);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
block_44:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = l_Lean_Syntax_getArgs(x_37);
lean_dec(x_37);
x_39 = lean_array_get_size(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
x_5 = x_35;
x_6 = x_38;
x_7 = x_41;
goto block_34;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(0);
x_43 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(x_35, x_42);
x_5 = x_35;
x_6 = x_38;
x_7 = x_43;
goto block_34;
}
}
block_47:
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_35 = x_46;
goto block_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_extern(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_23; uint8_t x_33; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_10);
x_33 = l_Lean_Environment_isProjectionFn(x_10, x_1);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc(x_1);
lean_inc(x_10);
x_34 = l_Lean_Environment_isConstructor(x_10, x_1);
x_23 = x_34;
goto block_32;
}
else
{
x_23 = x_33;
goto block_32;
}
block_22:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_add_extern(x_10, x_1);
x_14 = l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(x_13, x_11, x_12, x_8);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_15, x_12, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_32:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_1);
x_24 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_1);
lean_inc(x_10);
x_28 = l_Lean_Environment_find_x3f(x_10, x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_9);
x_11 = x_3;
x_12 = x_4;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 2)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_1);
x_30 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_9;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_9);
x_11 = x_3;
x_12 = x_4;
goto block_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed), 5, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed), 5, 0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("externAttr", 10, 10);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_mk_string_unchecked("extern", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("builtin and foreign functions", 29, 29);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_2);
x_15 = l_Lean_registerParametricAttribute(lean_box(0), x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1192_(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1192_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1192_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExternAttrData;
x_4 = l_Lean_externAttr;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint8_t x_16; uint32_t x_41; uint8_t x_42; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
lean_dec(x_1);
x_14 = lean_string_utf8_get(x_7, x_8);
x_15 = lean_unsigned_to_nat(48u);
x_41 = l_Char_ofNat(x_15);
x_42 = lean_uint32_dec_le(x_41, x_14);
if (x_42 == 0)
{
x_16 = x_42;
goto block_40;
}
else
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(57u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_uint32_dec_le(x_14, x_44);
x_16 = x_45;
goto block_40;
}
block_40:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_21);
x_22 = lean_unsigned_to_nat(10u);
x_23 = lean_nat_mul(x_3, x_22);
lean_dec(x_3);
x_24 = lean_uint32_to_nat(x_14);
x_25 = l_Char_ofNat(x_15);
x_26 = lean_uint32_to_nat(x_25);
x_27 = lean_nat_sub(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = lean_nat_add(x_23, x_27);
lean_dec(x_27);
lean_dec(x_23);
x_1 = x_13;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_30 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(10u);
x_33 = lean_nat_mul(x_3, x_32);
lean_dec(x_3);
x_34 = lean_uint32_to_nat(x_14);
x_35 = l_Char_ofNat(x_15);
x_36 = lean_uint32_to_nat(x_35);
x_37 = lean_nat_sub(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_38 = lean_nat_add(x_33, x_37);
lean_dec(x_37);
lean_dec(x_33);
x_1 = x_13;
x_2 = x_31;
x_3 = x_38;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_36; uint8_t x_37; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_36 = lean_string_utf8_byte_size(x_7);
x_37 = lean_nat_dec_lt(x_8, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
x_12 = x_6;
goto block_35;
}
else
{
x_12 = x_37;
goto block_35;
}
block_35:
{
uint8_t x_13; 
x_13 = l_instDecidableNot___redArg(x_12);
if (x_13 == 0)
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_14 = lean_string_utf8_get(x_7, x_8);
x_15 = lean_unsigned_to_nat(35u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_14, x_16);
x_18 = l_instDecidableNot___redArg(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_inc(x_19);
lean_inc(x_7);
if (lean_is_scalar(x_9)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_9;
}
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_22 = lean_nat_sub(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
x_23 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_22, x_20, x_5);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_sub(x_25, x_10);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_List_getD___redArg(x_1, x_26, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_4, x_28);
lean_dec(x_28);
x_2 = x_11;
x_3 = x_24;
x_4 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
if (lean_is_scalar(x_9)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_9;
}
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_string_push(x_4, x_14);
x_2 = x_11;
x_3 = x_32;
x_4 = x_33;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_4;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_string_length(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = l_Lean_expandExternPatternAux(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_expandExternPattern(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("(", 1, 1);
x_4 = lean_string_append(x_1, x_3);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked(", ", 2, 2);
x_7 = l_List_intersperseTR___redArg(x_6, x_2);
x_8 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_5, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked(")", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_4, 0);
x_6 = x_15;
goto block_14;
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_mk_string_unchecked("all", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_name_eq(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_name_eq(x_6, x_1);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; 
lean_inc(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_inc(x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_getExternEntryForAux(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_mk_string_unchecked("all", 3, 3);
x_17 = lean_string_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_18; 
x_18 = lean_unbox(x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = lean_unbox(x_13);
return x_19;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_14) == 0)
{
return x_17;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
x_20 = lean_unbox(x_13);
return x_20;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_21; 
x_21 = lean_unbox(x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
x_22 = lean_unbox(x_13);
return x_22;
}
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
x_23 = lean_unbox(x_13);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_7);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_extern_attr_data(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_getExternEntryFor(x_6, x_2);
lean_dec(x_6);
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
switch (lean_obj_tag(x_10)) {
case 2:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
case 3:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
default: 
{
lean_object* x_13; 
lean_free_object(x_7);
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
switch (lean_obj_tag(x_14)) {
case 2:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_box(0);
return x_19;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_97; lean_object* x_98; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed), 7, 0);
x_97 = lean_ctor_get(x_7, 0);
lean_inc(x_97);
lean_dec(x_7);
lean_inc(x_1);
x_98 = lean_get_extern_attr_data(x_97, x_1);
if (lean_obj_tag(x_98) == 0)
{
lean_free_object(x_5);
x_10 = x_2;
x_11 = x_3;
goto block_96;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_free_object(x_5);
x_10 = x_2;
x_11 = x_3;
goto block_96;
}
else
{
lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
lean_ctor_set(x_5, 0, x_101);
return x_5;
}
}
block_96:
{
lean_object* x_12; 
x_12 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_10, x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_to_nat(x_18);
x_20 = lean_nat_pow(x_16, x_19);
lean_dec(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_mk_empty_array_with_capacity(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_25);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_25);
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_inc(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_25);
lean_inc(x_25);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_inc(x_25);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_25);
lean_inc(x_26);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
lean_ctor_set(x_32, 8, x_31);
lean_inc(x_25);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_25);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_25);
lean_inc(x_25);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_25);
lean_inc(x_25);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_25);
lean_inc(x_36);
lean_inc(x_33);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_36);
lean_inc(x_23);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_23);
lean_inc(x_23);
x_39 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_24);
lean_ctor_set(x_39, 3, x_24);
lean_ctor_set_usize(x_39, 4, x_18);
lean_inc(x_25);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_25);
lean_inc_n(x_26, 2);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_15);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_st_mk_ref(x_42, x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_23);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_23);
x_47 = lean_box(1);
x_48 = lean_box(1);
x_49 = lean_box(0);
x_50 = lean_box(2);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_25);
x_52 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_23);
lean_ctor_set(x_52, 2, x_24);
lean_ctor_set(x_52, 3, x_24);
lean_ctor_set_usize(x_52, 4, x_18);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 0, 18);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 0, x_55);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 1, x_56);
x_57 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 2, x_57);
x_58 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 3, x_58);
x_59 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 4, x_59);
x_60 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 5, x_60);
x_61 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 6, x_61);
x_62 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, 7, x_62);
x_63 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 8, x_63);
x_64 = lean_unbox(x_48);
lean_ctor_set_uint8(x_54, 9, x_64);
x_65 = lean_unbox(x_49);
lean_ctor_set_uint8(x_54, 10, x_65);
x_66 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 11, x_66);
x_67 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 12, x_67);
x_68 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 13, x_68);
x_69 = lean_unbox(x_50);
lean_ctor_set_uint8(x_54, 14, x_69);
x_70 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 15, x_70);
x_71 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 16, x_71);
x_72 = lean_unbox(x_47);
lean_ctor_set_uint8(x_54, 17, x_72);
x_73 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_54);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_51);
lean_ctor_set(x_74, 1, x_52);
lean_ctor_set(x_74, 2, x_15);
x_75 = lean_mk_empty_array_with_capacity(x_24);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = l_Lean_ConstantInfo_type(x_13);
lean_dec(x_13);
x_79 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_79, 0, x_54);
lean_ctor_set(x_79, 1, x_15);
lean_ctor_set(x_79, 2, x_74);
lean_ctor_set(x_79, 3, x_75);
lean_ctor_set(x_79, 4, x_76);
lean_ctor_set(x_79, 5, x_24);
lean_ctor_set(x_79, 6, x_77);
lean_ctor_set_uint64(x_79, sizeof(void*)*7, x_73);
x_80 = lean_unbox(x_53);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 8, x_80);
x_81 = lean_unbox(x_53);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 9, x_81);
x_82 = lean_unbox(x_53);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 10, x_82);
x_83 = lean_unbox(x_53);
lean_inc(x_44);
x_84 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_78, x_9, x_83, x_79, x_44, x_10, x_11, x_45);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_get(x_44, x_86);
lean_dec(x_44);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_dec(x_44);
return x_84;
}
}
else
{
uint8_t x_92; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_92 = !lean_is_exclusive(x_12);
if (x_92 == 0)
{
return x_12;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_191; lean_object* x_192; 
x_102 = lean_ctor_get(x_5, 0);
x_103 = lean_ctor_get(x_5, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_5);
x_104 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed), 7, 0);
x_191 = lean_ctor_get(x_102, 0);
lean_inc(x_191);
lean_dec(x_102);
lean_inc(x_1);
x_192 = lean_get_extern_attr_data(x_191, x_1);
if (lean_obj_tag(x_192) == 0)
{
x_105 = x_2;
x_106 = x_3;
goto block_190;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
x_105 = x_2;
x_106 = x_3;
goto block_190;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_104);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_103);
return x_196;
}
}
block_190:
{
lean_object* x_107; 
x_107 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_105, x_106, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint64_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; lean_object* x_179; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_unsigned_to_nat(5u);
x_113 = lean_usize_of_nat(x_112);
x_114 = lean_usize_to_nat(x_113);
x_115 = lean_nat_pow(x_111, x_114);
lean_dec(x_114);
x_116 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_117 = lean_usize_to_nat(x_116);
x_118 = lean_mk_empty_array_with_capacity(x_117);
lean_dec(x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_120);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc(x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_120);
lean_inc(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_120);
lean_inc(x_120);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_120);
lean_inc(x_120);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_120);
lean_inc(x_120);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_120);
lean_inc(x_121);
x_127 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_127, 0, x_119);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_119);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 5, x_123);
lean_ctor_set(x_127, 6, x_124);
lean_ctor_set(x_127, 7, x_125);
lean_ctor_set(x_127, 8, x_126);
lean_inc(x_120);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_120);
lean_inc(x_120);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_120);
lean_inc(x_120);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_120);
lean_inc(x_120);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_120);
lean_inc(x_131);
lean_inc(x_128);
x_132 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_128);
lean_ctor_set(x_132, 4, x_131);
lean_ctor_set(x_132, 5, x_131);
lean_inc(x_118);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_118);
lean_inc(x_118);
x_134 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_118);
lean_ctor_set(x_134, 2, x_119);
lean_ctor_set(x_134, 3, x_119);
lean_ctor_set_usize(x_134, 4, x_113);
lean_inc(x_120);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_120);
lean_inc_n(x_121, 2);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_121);
lean_ctor_set(x_136, 2, x_121);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_137, 2, x_110);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_136);
x_138 = lean_st_mk_ref(x_137, x_109);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_118);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_118);
x_142 = lean_box(1);
x_143 = lean_box(1);
x_144 = lean_box(0);
x_145 = lean_box(2);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_120);
x_147 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_118);
lean_ctor_set(x_147, 2, x_119);
lean_ctor_set(x_147, 3, x_119);
lean_ctor_set_usize(x_147, 4, x_113);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 0, 18);
x_150 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 0, x_150);
x_151 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 1, x_151);
x_152 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 2, x_152);
x_153 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 3, x_153);
x_154 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 4, x_154);
x_155 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 5, x_155);
x_156 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 6, x_156);
x_157 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, 7, x_157);
x_158 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 8, x_158);
x_159 = lean_unbox(x_143);
lean_ctor_set_uint8(x_149, 9, x_159);
x_160 = lean_unbox(x_144);
lean_ctor_set_uint8(x_149, 10, x_160);
x_161 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 11, x_161);
x_162 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 12, x_162);
x_163 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 13, x_163);
x_164 = lean_unbox(x_145);
lean_ctor_set_uint8(x_149, 14, x_164);
x_165 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 15, x_165);
x_166 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 16, x_166);
x_167 = lean_unbox(x_142);
lean_ctor_set_uint8(x_149, 17, x_167);
x_168 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_149);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_146);
lean_ctor_set(x_169, 1, x_147);
lean_ctor_set(x_169, 2, x_110);
x_170 = lean_mk_empty_array_with_capacity(x_119);
x_171 = lean_box(0);
x_172 = lean_box(0);
x_173 = l_Lean_ConstantInfo_type(x_108);
lean_dec(x_108);
x_174 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_174, 0, x_149);
lean_ctor_set(x_174, 1, x_110);
lean_ctor_set(x_174, 2, x_169);
lean_ctor_set(x_174, 3, x_170);
lean_ctor_set(x_174, 4, x_171);
lean_ctor_set(x_174, 5, x_119);
lean_ctor_set(x_174, 6, x_172);
lean_ctor_set_uint64(x_174, sizeof(void*)*7, x_168);
x_175 = lean_unbox(x_148);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 8, x_175);
x_176 = lean_unbox(x_148);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 9, x_176);
x_177 = lean_unbox(x_148);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 10, x_177);
x_178 = lean_unbox(x_148);
lean_inc(x_139);
x_179 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_173, x_104, x_178, x_174, x_139, x_105, x_106, x_140);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_st_ref_get(x_139, x_181);
lean_dec(x_139);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_180);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
else
{
lean_dec(x_139);
return x_179;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
x_186 = lean_ctor_get(x_107, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_107, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_188 = x_107;
} else {
 lean_dec_ref(x_107);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_mk_string_unchecked("_uniq", 5, 5);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_nat_pow(x_9, x_12);
lean_dec(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_io_get_num_heartbeats(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Name_mkStr1(x_8);
x_28 = lean_uint64_of_nat(x_25);
lean_inc(x_16);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set_usize(x_29, 4, x_11);
lean_inc(x_18);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_18);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_usize(x_31, 4, x_11);
x_32 = lean_box(0);
x_33 = lean_box(1);
lean_inc(x_18);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_18);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_18);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set_usize(x_36, 4, x_11);
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_28);
lean_inc(x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_30);
lean_inc(x_31);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_36);
x_41 = lean_unbox(x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_41);
x_42 = lean_mk_empty_array_with_capacity(x_25);
lean_inc(x_38);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_21);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set(x_43, 7, x_42);
x_44 = lean_st_mk_ref(x_43, x_24);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_inheritedTraceOptions;
x_48 = lean_st_ref_get(x_47, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_45, x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_105; uint8_t x_106; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Array_empty(lean_box(0));
x_57 = lean_mk_string_unchecked("<compiler>", 10, 10);
lean_ctor_set(x_51, 1, x_56);
lean_ctor_set(x_51, 0, x_55);
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = lean_box(0);
x_61 = lean_box(0);
x_62 = l_Lean_Core_getMaxHeartbeats(x_58);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = l_Lean_diagnostics;
x_66 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_58, x_65);
x_105 = lean_ctor_get(x_53, 0);
lean_inc(x_105);
lean_dec(x_53);
x_106 = l_Lean_Kernel_isDiagnosticsEnabled(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
if (x_66 == 0)
{
lean_dec(x_38);
lean_inc(x_45);
x_67 = x_45;
x_68 = x_54;
goto block_89;
}
else
{
goto block_104;
}
}
else
{
if (x_66 == 0)
{
goto block_104;
}
else
{
lean_dec(x_38);
lean_inc(x_45);
x_67 = x_45;
x_68 = x_54;
goto block_89;
}
}
block_89:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_69 = l_Lean_maxRecDepth;
x_70 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_58, x_69);
x_71 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_51);
lean_ctor_set(x_71, 2, x_58);
lean_ctor_set(x_71, 3, x_25);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_59);
lean_ctor_set(x_71, 6, x_60);
lean_ctor_set(x_71, 7, x_61);
lean_ctor_set(x_71, 8, x_23);
lean_ctor_set(x_71, 9, x_62);
lean_ctor_set(x_71, 10, x_26);
lean_ctor_set(x_71, 11, x_64);
lean_ctor_set(x_71, 12, x_49);
lean_ctor_set_uint8(x_71, sizeof(void*)*13, x_66);
x_72 = lean_unbox(x_63);
lean_ctor_set_uint8(x_71, sizeof(void*)*13 + 1, x_72);
x_73 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_2, x_71, x_67, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_45, x_75);
lean_dec(x_45);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_45);
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_dec(x_73);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_MessageData_toString(x_85, x_84);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_4 = x_87;
goto block_7;
}
else
{
lean_object* x_88; 
lean_dec(x_83);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_4 = x_88;
goto block_7;
}
}
}
block_104:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_st_ref_take(x_45, x_54);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = l_Lean_Kernel_enableDiag(x_93, x_66);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 7);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_95);
lean_ctor_set(x_101, 2, x_96);
lean_ctor_set(x_101, 3, x_97);
lean_ctor_set(x_101, 4, x_38);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set(x_101, 7, x_100);
x_102 = lean_st_ref_set(x_45, x_101, x_92);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_45);
x_67 = x_45;
x_68 = x_103;
goto block_89;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_158; uint8_t x_159; 
x_107 = lean_ctor_get(x_51, 0);
x_108 = lean_ctor_get(x_51, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_51);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Array_empty(lean_box(0));
x_111 = lean_mk_string_unchecked("<compiler>", 10, 10);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_box(0);
x_114 = lean_box(0);
x_115 = lean_box(0);
x_116 = lean_box(0);
x_117 = l_Lean_Core_getMaxHeartbeats(x_113);
x_118 = lean_box(0);
x_119 = lean_box(0);
x_120 = l_Lean_diagnostics;
x_121 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_113, x_120);
x_158 = lean_ctor_get(x_107, 0);
lean_inc(x_158);
lean_dec(x_107);
x_159 = l_Lean_Kernel_isDiagnosticsEnabled(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
if (x_121 == 0)
{
lean_dec(x_38);
lean_inc(x_45);
x_122 = x_45;
x_123 = x_108;
goto block_142;
}
else
{
goto block_157;
}
}
else
{
if (x_121 == 0)
{
goto block_157;
}
else
{
lean_dec(x_38);
lean_inc(x_45);
x_122 = x_45;
x_123 = x_108;
goto block_142;
}
}
block_142:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
x_124 = l_Lean_maxRecDepth;
x_125 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_113, x_124);
x_126 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_112);
lean_ctor_set(x_126, 2, x_113);
lean_ctor_set(x_126, 3, x_25);
lean_ctor_set(x_126, 4, x_125);
lean_ctor_set(x_126, 5, x_114);
lean_ctor_set(x_126, 6, x_115);
lean_ctor_set(x_126, 7, x_116);
lean_ctor_set(x_126, 8, x_23);
lean_ctor_set(x_126, 9, x_117);
lean_ctor_set(x_126, 10, x_26);
lean_ctor_set(x_126, 11, x_119);
lean_ctor_set(x_126, 12, x_49);
lean_ctor_set_uint8(x_126, sizeof(void*)*13, x_121);
x_127 = lean_unbox(x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*13 + 1, x_127);
x_128 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_2, x_126, x_122, x_123);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_st_ref_get(x_45, x_130);
lean_dec(x_45);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_129);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_45);
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_MessageData_toString(x_138, x_137);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_4 = x_140;
goto block_7;
}
else
{
lean_object* x_141; 
lean_dec(x_136);
x_141 = lean_ctor_get(x_128, 1);
lean_inc(x_141);
lean_dec(x_128);
x_4 = x_141;
goto block_7;
}
}
}
block_157:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_143 = lean_st_ref_take(x_45, x_108);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = l_Lean_Kernel_enableDiag(x_146, x_121);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_144, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 5);
lean_inc(x_151);
x_152 = lean_ctor_get(x_144, 6);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 7);
lean_inc(x_153);
lean_dec(x_144);
x_154 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 3, x_150);
lean_ctor_set(x_154, 4, x_38);
lean_ctor_set(x_154, 5, x_151);
lean_ctor_set(x_154, 6, x_152);
lean_ctor_set(x_154, 7, x_153);
x_155 = lean_st_ref_set(x_45, x_154, x_145);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_45);
x_122 = x_45;
x_123 = x_156;
goto block_142;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint64_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_242; uint8_t x_243; 
x_160 = lean_ctor_get(x_21, 0);
x_161 = lean_ctor_get(x_21, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_21);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_unsigned_to_nat(1u);
x_164 = l_Lean_Name_mkStr1(x_8);
x_165 = lean_uint64_of_nat(x_162);
lean_inc(x_16);
x_166 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_166, 0, x_17);
lean_ctor_set(x_166, 1, x_16);
lean_ctor_set(x_166, 2, x_162);
lean_ctor_set(x_166, 3, x_162);
lean_ctor_set_usize(x_166, 4, x_11);
lean_inc(x_18);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_18);
lean_inc(x_16);
x_168 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_168, 0, x_19);
lean_ctor_set(x_168, 1, x_16);
lean_ctor_set(x_168, 2, x_162);
lean_ctor_set(x_168, 3, x_162);
lean_ctor_set_usize(x_168, 4, x_11);
x_169 = lean_box(0);
x_170 = lean_box(1);
lean_inc(x_18);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_18);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_18);
x_173 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_173, 0, x_20);
lean_ctor_set(x_173, 1, x_16);
lean_ctor_set(x_173, 2, x_162);
lean_ctor_set(x_173, 3, x_162);
lean_ctor_set_usize(x_173, 4, x_11);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_163);
x_175 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set_uint64(x_175, sizeof(void*)*1, x_165);
lean_inc(x_167);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_167);
lean_ctor_set(x_176, 1, x_167);
lean_inc(x_168);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_168);
lean_ctor_set(x_177, 2, x_169);
x_178 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
x_179 = lean_unbox(x_170);
lean_ctor_set_uint8(x_178, sizeof(void*)*3, x_179);
x_180 = lean_mk_empty_array_with_capacity(x_162);
lean_inc(x_176);
x_181 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_181, 0, x_1);
lean_ctor_set(x_181, 1, x_9);
lean_ctor_set(x_181, 2, x_174);
lean_ctor_set(x_181, 3, x_175);
lean_ctor_set(x_181, 4, x_176);
lean_ctor_set(x_181, 5, x_177);
lean_ctor_set(x_181, 6, x_178);
lean_ctor_set(x_181, 7, x_180);
x_182 = lean_st_mk_ref(x_181, x_161);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_inheritedTraceOptions;
x_186 = lean_st_ref_get(x_185, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_st_ref_get(x_183, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_mk_string_unchecked("", 0, 0);
x_194 = l_Array_empty(lean_box(0));
x_195 = lean_mk_string_unchecked("<compiler>", 10, 10);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_box(0);
x_198 = lean_box(0);
x_199 = lean_box(0);
x_200 = lean_box(0);
x_201 = l_Lean_Core_getMaxHeartbeats(x_197);
x_202 = lean_box(0);
x_203 = lean_box(0);
x_204 = l_Lean_diagnostics;
x_205 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_197, x_204);
x_242 = lean_ctor_get(x_190, 0);
lean_inc(x_242);
lean_dec(x_190);
x_243 = l_Lean_Kernel_isDiagnosticsEnabled(x_242);
lean_dec(x_242);
if (x_243 == 0)
{
if (x_205 == 0)
{
lean_dec(x_176);
lean_inc(x_183);
x_206 = x_183;
x_207 = x_191;
goto block_226;
}
else
{
goto block_241;
}
}
else
{
if (x_205 == 0)
{
goto block_241;
}
else
{
lean_dec(x_176);
lean_inc(x_183);
x_206 = x_183;
x_207 = x_191;
goto block_226;
}
}
block_226:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_208 = l_Lean_maxRecDepth;
x_209 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_197, x_208);
x_210 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_210, 0, x_195);
lean_ctor_set(x_210, 1, x_196);
lean_ctor_set(x_210, 2, x_197);
lean_ctor_set(x_210, 3, x_162);
lean_ctor_set(x_210, 4, x_209);
lean_ctor_set(x_210, 5, x_198);
lean_ctor_set(x_210, 6, x_199);
lean_ctor_set(x_210, 7, x_200);
lean_ctor_set(x_210, 8, x_160);
lean_ctor_set(x_210, 9, x_201);
lean_ctor_set(x_210, 10, x_163);
lean_ctor_set(x_210, 11, x_203);
lean_ctor_set(x_210, 12, x_187);
lean_ctor_set_uint8(x_210, sizeof(void*)*13, x_205);
x_211 = lean_unbox(x_202);
lean_ctor_set_uint8(x_210, sizeof(void*)*13 + 1, x_211);
x_212 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_2, x_210, x_206, x_207);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_st_ref_get(x_183, x_214);
lean_dec(x_183);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
else
{
lean_object* x_220; 
lean_dec(x_183);
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_MessageData_toString(x_222, x_221);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_4 = x_224;
goto block_7;
}
else
{
lean_object* x_225; 
lean_dec(x_220);
x_225 = lean_ctor_get(x_212, 1);
lean_inc(x_225);
lean_dec(x_212);
x_4 = x_225;
goto block_7;
}
}
}
block_241:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_227 = lean_st_ref_take(x_183, x_191);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
x_231 = l_Lean_Kernel_enableDiag(x_230, x_205);
x_232 = lean_ctor_get(x_228, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_228, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_228, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_228, 5);
lean_inc(x_235);
x_236 = lean_ctor_get(x_228, 6);
lean_inc(x_236);
x_237 = lean_ctor_get(x_228, 7);
lean_inc(x_237);
lean_dec(x_228);
x_238 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set(x_238, 1, x_232);
lean_ctor_set(x_238, 2, x_233);
lean_ctor_set(x_238, 3, x_234);
lean_ctor_set(x_238, 4, x_176);
lean_ctor_set(x_238, 5, x_235);
lean_ctor_set(x_238, 6, x_236);
lean_ctor_set(x_238, 7, x_237);
x_239 = lean_st_ref_set(x_183, x_238, x_229);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
lean_inc(x_183);
x_206 = x_183;
x_207 = x_240;
goto block_226;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instBEqExternEntry = _init_l_Lean_instBEqExternEntry();
lean_mark_persistent(l_Lean_instBEqExternEntry);
l_Lean_instHashableExternEntry = _init_l_Lean_instHashableExternEntry();
lean_mark_persistent(l_Lean_instHashableExternEntry);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
l_Lean_instBEqExternAttrData = _init_l_Lean_instBEqExternAttrData();
lean_mark_persistent(l_Lean_instBEqExternAttrData);
l_Lean_instHashableExternAttrData = _init_l_Lean_instHashableExternAttrData();
lean_mark_persistent(l_Lean_instHashableExternAttrData);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
