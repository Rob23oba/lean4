// Lean compiler output
// Module: Lean.Compiler.CSimpAttr
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Util.ReplaceExpr
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
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasCSimpAttribute___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedEntry;
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasCSimpAttribute(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object*);
lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_ext;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_switch(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
x_8 = l_Nat_nextPowerOfTwo(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unbox(x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unbox(x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_switch(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(x_3);
lean_dec(x_3);
x_6 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(x_7);
lean_dec(x_7);
x_10 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_Namespace___hyg_3__spec__4___redArg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_CSimp_State_switch(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_4, x_6, x_7);
x_10 = lean_box(0);
x_11 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_5, x_8, x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_12, x_14, x_15);
x_18 = lean_box(0);
x_19 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_13, x_16, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_137_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_137_), 2, 0);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Compiler", 8, 8);
x_6 = lean_mk_string_unchecked("CSimp", 5, 5);
x_7 = lean_mk_string_unchecked("ext", 3, 3);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_box(1);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_10, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_19);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unbox(x_9);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unbox(x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_2);
x_29 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_28, x_1);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Eq", 2, 2);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_free_object(x_5);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_14, x_2, x_3, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Expr_appFn_x21(x_9);
x_17 = l_Lean_Expr_appFn_x21(x_16);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
x_19 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_20 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_5);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_bvar___override(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_25, x_2, x_3, x_8);
lean_dec(x_25);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_5);
lean_dec(x_1);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_Expr_fvar___override(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_31, x_2, x_3, x_8);
lean_dec(x_31);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_5);
lean_dec(x_1);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_34 = l_Lean_Expr_mvar___override(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_37, x_2, x_3, x_8);
lean_dec(x_37);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_5);
lean_dec(x_1);
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
lean_dec(x_19);
x_40 = l_Lean_Expr_sort___override(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_20);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_43, x_2, x_3, x_8);
lean_dec(x_43);
return x_44;
}
case 4:
{
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_ctor_get(x_20, 0);
lean_inc(x_47);
lean_dec(x_20);
x_48 = l_Lean_Expr_const___override(x_45, x_46);
x_49 = l_Lean_Expr_bvar___override(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_52, x_2, x_3, x_8);
lean_dec(x_52);
return x_53;
}
case 1:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_5);
lean_dec(x_1);
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_dec(x_19);
x_56 = lean_ctor_get(x_20, 0);
lean_inc(x_56);
lean_dec(x_20);
x_57 = l_Lean_Expr_const___override(x_54, x_55);
x_58 = l_Lean_Expr_fvar___override(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_18);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_61, x_2, x_3, x_8);
lean_dec(x_61);
return x_62;
}
case 2:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_5);
lean_dec(x_1);
x_63 = lean_ctor_get(x_19, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_dec(x_19);
x_65 = lean_ctor_get(x_20, 0);
lean_inc(x_65);
lean_dec(x_20);
x_66 = l_Lean_Expr_const___override(x_63, x_64);
x_67 = l_Lean_Expr_mvar___override(x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_70, x_2, x_3, x_8);
lean_dec(x_70);
return x_71;
}
case 3:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_5);
lean_dec(x_1);
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_ctor_get(x_20, 0);
lean_inc(x_74);
lean_dec(x_20);
x_75 = l_Lean_Expr_const___override(x_72, x_73);
x_76 = l_Lean_Expr_sort___override(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_18);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_79, x_2, x_3, x_8);
lean_dec(x_79);
return x_80;
}
case 4:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_18);
x_81 = lean_ctor_get(x_19, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_19, 1);
lean_inc(x_82);
lean_dec(x_19);
x_83 = lean_ctor_get(x_20, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_20, 1);
lean_inc(x_84);
lean_dec(x_20);
x_85 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_82, x_84);
lean_dec(x_84);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_1);
x_86 = lean_box(0);
lean_ctor_set(x_5, 0, x_86);
return x_5;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_1);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_5, 0, x_88);
return x_5;
}
}
case 5:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_5);
lean_dec(x_1);
x_89 = lean_ctor_get(x_19, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_19, 1);
lean_inc(x_90);
lean_dec(x_19);
x_91 = lean_ctor_get(x_20, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_20, 1);
lean_inc(x_92);
lean_dec(x_20);
x_93 = l_Lean_Expr_const___override(x_89, x_90);
x_94 = l_Lean_Expr_app___override(x_91, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_18);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_97, x_2, x_3, x_8);
lean_dec(x_97);
return x_98;
}
case 6:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_5);
lean_dec(x_1);
x_99 = lean_ctor_get(x_19, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
lean_dec(x_19);
x_101 = lean_ctor_get(x_20, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_20, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_20, 2);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_105 = l_Lean_Expr_const___override(x_99, x_100);
x_106 = l_Lean_Expr_lam___override(x_101, x_102, x_103, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_18);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_109, x_2, x_3, x_8);
lean_dec(x_109);
return x_110;
}
case 7:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_free_object(x_5);
lean_dec(x_1);
x_111 = lean_ctor_get(x_19, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_19, 1);
lean_inc(x_112);
lean_dec(x_19);
x_113 = lean_ctor_get(x_20, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_20, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_20, 2);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_117 = l_Lean_Expr_const___override(x_111, x_112);
x_118 = l_Lean_Expr_forallE___override(x_113, x_114, x_115, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_18);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_121, x_2, x_3, x_8);
lean_dec(x_121);
return x_122;
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_free_object(x_5);
lean_dec(x_1);
x_123 = lean_ctor_get(x_19, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_19, 1);
lean_inc(x_124);
lean_dec(x_19);
x_125 = lean_ctor_get(x_20, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_20, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_20, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_20, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_20, sizeof(void*)*4 + 8);
lean_dec(x_20);
x_130 = l_Lean_Expr_const___override(x_123, x_124);
x_131 = l_Lean_Expr_letE___override(x_125, x_126, x_127, x_128, x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_18);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_134, x_2, x_3, x_8);
lean_dec(x_134);
return x_135;
}
case 9:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_5);
lean_dec(x_1);
x_136 = lean_ctor_get(x_19, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_19, 1);
lean_inc(x_137);
lean_dec(x_19);
x_138 = lean_ctor_get(x_20, 0);
lean_inc(x_138);
lean_dec(x_20);
x_139 = l_Lean_Expr_const___override(x_136, x_137);
x_140 = l_Lean_Expr_lit___override(x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_18);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_143, x_2, x_3, x_8);
lean_dec(x_143);
return x_144;
}
case 10:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_free_object(x_5);
lean_dec(x_1);
x_145 = lean_ctor_get(x_19, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_19, 1);
lean_inc(x_146);
lean_dec(x_19);
x_147 = lean_ctor_get(x_20, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_20, 1);
lean_inc(x_148);
lean_dec(x_20);
x_149 = l_Lean_Expr_const___override(x_145, x_146);
x_150 = l_Lean_Expr_mdata___override(x_147, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_18);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_153, x_2, x_3, x_8);
lean_dec(x_153);
return x_154;
}
default: 
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_5);
lean_dec(x_1);
x_155 = lean_ctor_get(x_19, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_19, 1);
lean_inc(x_156);
lean_dec(x_19);
x_157 = lean_ctor_get(x_20, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_20, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_20, 2);
lean_inc(x_159);
lean_dec(x_20);
x_160 = l_Lean_Expr_const___override(x_155, x_156);
x_161 = l_Lean_Expr_proj___override(x_157, x_158, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_18);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_164, x_2, x_3, x_8);
lean_dec(x_164);
return x_165;
}
}
}
case 5:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_free_object(x_5);
lean_dec(x_1);
x_166 = lean_ctor_get(x_19, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_19, 1);
lean_inc(x_167);
lean_dec(x_19);
x_168 = l_Lean_Expr_app___override(x_166, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_20);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_18);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_171, x_2, x_3, x_8);
lean_dec(x_171);
return x_172;
}
case 6:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_free_object(x_5);
lean_dec(x_1);
x_173 = lean_ctor_get(x_19, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_19, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_19, 2);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 8);
lean_dec(x_19);
x_177 = l_Lean_Expr_lam___override(x_173, x_174, x_175, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_20);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_18);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_180, x_2, x_3, x_8);
lean_dec(x_180);
return x_181;
}
case 7:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_free_object(x_5);
lean_dec(x_1);
x_182 = lean_ctor_get(x_19, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_19, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_19, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 8);
lean_dec(x_19);
x_186 = l_Lean_Expr_forallE___override(x_182, x_183, x_184, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_20);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_18);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_189, x_2, x_3, x_8);
lean_dec(x_189);
return x_190;
}
case 8:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_free_object(x_5);
lean_dec(x_1);
x_191 = lean_ctor_get(x_19, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_19, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_19, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_19, 3);
lean_inc(x_194);
x_195 = lean_ctor_get_uint8(x_19, sizeof(void*)*4 + 8);
lean_dec(x_19);
x_196 = l_Lean_Expr_letE___override(x_191, x_192, x_193, x_194, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_20);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_18);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_199, x_2, x_3, x_8);
lean_dec(x_199);
return x_200;
}
case 9:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_free_object(x_5);
lean_dec(x_1);
x_201 = lean_ctor_get(x_19, 0);
lean_inc(x_201);
lean_dec(x_19);
x_202 = l_Lean_Expr_lit___override(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_20);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_18);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_205, x_2, x_3, x_8);
lean_dec(x_205);
return x_206;
}
case 10:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_free_object(x_5);
lean_dec(x_1);
x_207 = lean_ctor_get(x_19, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_19, 1);
lean_inc(x_208);
lean_dec(x_19);
x_209 = l_Lean_Expr_mdata___override(x_207, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_20);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_18);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_212, x_2, x_3, x_8);
lean_dec(x_212);
return x_213;
}
default: 
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_free_object(x_5);
lean_dec(x_1);
x_214 = lean_ctor_get(x_19, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_19, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_19, 2);
lean_inc(x_216);
lean_dec(x_19);
x_217 = l_Lean_Expr_proj___override(x_214, x_215, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_20);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_18);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_220, x_2, x_3, x_8);
lean_dec(x_220);
return x_221;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_222 = lean_ctor_get(x_5, 0);
x_223 = lean_ctor_get(x_5, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_5);
x_224 = l_Lean_ConstantInfo_type(x_222);
lean_dec(x_222);
x_225 = lean_mk_string_unchecked("Eq", 2, 2);
x_226 = l_Lean_Name_mkStr1(x_225);
x_227 = lean_unsigned_to_nat(3u);
x_228 = l_Lean_Expr_isAppOfArity(x_224, x_226, x_227);
lean_dec(x_226);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_224);
lean_dec(x_1);
x_229 = lean_box(0);
x_230 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_229, x_2, x_3, x_223);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = l_Lean_Expr_appFn_x21(x_224);
x_232 = l_Lean_Expr_appFn_x21(x_231);
x_233 = l_Lean_Expr_appArg_x21(x_232);
lean_dec(x_232);
x_234 = l_Lean_Expr_appArg_x21(x_231);
lean_dec(x_231);
x_235 = l_Lean_Expr_appArg_x21(x_224);
lean_dec(x_224);
switch (lean_obj_tag(x_234)) {
case 0:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_1);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_Expr_bvar___override(x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_240, x_2, x_3, x_223);
lean_dec(x_240);
return x_241;
}
case 1:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_1);
x_242 = lean_ctor_get(x_234, 0);
lean_inc(x_242);
lean_dec(x_234);
x_243 = l_Lean_Expr_fvar___override(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_235);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_233);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_246, x_2, x_3, x_223);
lean_dec(x_246);
return x_247;
}
case 2:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_1);
x_248 = lean_ctor_get(x_234, 0);
lean_inc(x_248);
lean_dec(x_234);
x_249 = l_Lean_Expr_mvar___override(x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_235);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_233);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_252, x_2, x_3, x_223);
lean_dec(x_252);
return x_253;
}
case 3:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_1);
x_254 = lean_ctor_get(x_234, 0);
lean_inc(x_254);
lean_dec(x_234);
x_255 = l_Lean_Expr_sort___override(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_235);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_233);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_258, x_2, x_3, x_223);
lean_dec(x_258);
return x_259;
}
case 4:
{
switch (lean_obj_tag(x_235)) {
case 0:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_1);
x_260 = lean_ctor_get(x_234, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_234, 1);
lean_inc(x_261);
lean_dec(x_234);
x_262 = lean_ctor_get(x_235, 0);
lean_inc(x_262);
lean_dec(x_235);
x_263 = l_Lean_Expr_const___override(x_260, x_261);
x_264 = l_Lean_Expr_bvar___override(x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_233);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_267, x_2, x_3, x_223);
lean_dec(x_267);
return x_268;
}
case 1:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_1);
x_269 = lean_ctor_get(x_234, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_234, 1);
lean_inc(x_270);
lean_dec(x_234);
x_271 = lean_ctor_get(x_235, 0);
lean_inc(x_271);
lean_dec(x_235);
x_272 = l_Lean_Expr_const___override(x_269, x_270);
x_273 = l_Lean_Expr_fvar___override(x_271);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_233);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_276, x_2, x_3, x_223);
lean_dec(x_276);
return x_277;
}
case 2:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_1);
x_278 = lean_ctor_get(x_234, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_234, 1);
lean_inc(x_279);
lean_dec(x_234);
x_280 = lean_ctor_get(x_235, 0);
lean_inc(x_280);
lean_dec(x_235);
x_281 = l_Lean_Expr_const___override(x_278, x_279);
x_282 = l_Lean_Expr_mvar___override(x_280);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_233);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_285, x_2, x_3, x_223);
lean_dec(x_285);
return x_286;
}
case 3:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_1);
x_287 = lean_ctor_get(x_234, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_234, 1);
lean_inc(x_288);
lean_dec(x_234);
x_289 = lean_ctor_get(x_235, 0);
lean_inc(x_289);
lean_dec(x_235);
x_290 = l_Lean_Expr_const___override(x_287, x_288);
x_291 = l_Lean_Expr_sort___override(x_289);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_233);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_295 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_294, x_2, x_3, x_223);
lean_dec(x_294);
return x_295;
}
case 4:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_dec(x_233);
x_296 = lean_ctor_get(x_234, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_234, 1);
lean_inc(x_297);
lean_dec(x_234);
x_298 = lean_ctor_get(x_235, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_235, 1);
lean_inc(x_299);
lean_dec(x_235);
x_300 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_297, x_299);
lean_dec(x_299);
lean_dec(x_297);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_1);
x_301 = lean_box(0);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_223);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_303, 0, x_296);
lean_ctor_set(x_303, 1, x_298);
lean_ctor_set(x_303, 2, x_1);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_223);
return x_305;
}
}
case 5:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_1);
x_306 = lean_ctor_get(x_234, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_234, 1);
lean_inc(x_307);
lean_dec(x_234);
x_308 = lean_ctor_get(x_235, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_235, 1);
lean_inc(x_309);
lean_dec(x_235);
x_310 = l_Lean_Expr_const___override(x_306, x_307);
x_311 = l_Lean_Expr_app___override(x_308, x_309);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_233);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
x_315 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_314, x_2, x_3, x_223);
lean_dec(x_314);
return x_315;
}
case 6:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_1);
x_316 = lean_ctor_get(x_234, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_234, 1);
lean_inc(x_317);
lean_dec(x_234);
x_318 = lean_ctor_get(x_235, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_235, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_235, 2);
lean_inc(x_320);
x_321 = lean_ctor_get_uint8(x_235, sizeof(void*)*3 + 8);
lean_dec(x_235);
x_322 = l_Lean_Expr_const___override(x_316, x_317);
x_323 = l_Lean_Expr_lam___override(x_318, x_319, x_320, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_233);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_326, x_2, x_3, x_223);
lean_dec(x_326);
return x_327;
}
case 7:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_1);
x_328 = lean_ctor_get(x_234, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_234, 1);
lean_inc(x_329);
lean_dec(x_234);
x_330 = lean_ctor_get(x_235, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_235, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_235, 2);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_235, sizeof(void*)*3 + 8);
lean_dec(x_235);
x_334 = l_Lean_Expr_const___override(x_328, x_329);
x_335 = l_Lean_Expr_forallE___override(x_330, x_331, x_332, x_333);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_233);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_339 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_338, x_2, x_3, x_223);
lean_dec(x_338);
return x_339;
}
case 8:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_1);
x_340 = lean_ctor_get(x_234, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_234, 1);
lean_inc(x_341);
lean_dec(x_234);
x_342 = lean_ctor_get(x_235, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_235, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_235, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_235, 3);
lean_inc(x_345);
x_346 = lean_ctor_get_uint8(x_235, sizeof(void*)*4 + 8);
lean_dec(x_235);
x_347 = l_Lean_Expr_const___override(x_340, x_341);
x_348 = l_Lean_Expr_letE___override(x_342, x_343, x_344, x_345, x_346);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_233);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
x_352 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_351, x_2, x_3, x_223);
lean_dec(x_351);
return x_352;
}
case 9:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_1);
x_353 = lean_ctor_get(x_234, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_234, 1);
lean_inc(x_354);
lean_dec(x_234);
x_355 = lean_ctor_get(x_235, 0);
lean_inc(x_355);
lean_dec(x_235);
x_356 = l_Lean_Expr_const___override(x_353, x_354);
x_357 = l_Lean_Expr_lit___override(x_355);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_233);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_359);
x_361 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_360, x_2, x_3, x_223);
lean_dec(x_360);
return x_361;
}
case 10:
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_1);
x_362 = lean_ctor_get(x_234, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_234, 1);
lean_inc(x_363);
lean_dec(x_234);
x_364 = lean_ctor_get(x_235, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_235, 1);
lean_inc(x_365);
lean_dec(x_235);
x_366 = l_Lean_Expr_const___override(x_362, x_363);
x_367 = l_Lean_Expr_mdata___override(x_364, x_365);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_233);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
x_371 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_370, x_2, x_3, x_223);
lean_dec(x_370);
return x_371;
}
default: 
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_1);
x_372 = lean_ctor_get(x_234, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_234, 1);
lean_inc(x_373);
lean_dec(x_234);
x_374 = lean_ctor_get(x_235, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_235, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_235, 2);
lean_inc(x_376);
lean_dec(x_235);
x_377 = l_Lean_Expr_const___override(x_372, x_373);
x_378 = l_Lean_Expr_proj___override(x_374, x_375, x_376);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_233);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_380);
x_382 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_381, x_2, x_3, x_223);
lean_dec(x_381);
return x_382;
}
}
}
case 5:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_1);
x_383 = lean_ctor_get(x_234, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_234, 1);
lean_inc(x_384);
lean_dec(x_234);
x_385 = l_Lean_Expr_app___override(x_383, x_384);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_235);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_233);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_387);
x_389 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_388, x_2, x_3, x_223);
lean_dec(x_388);
return x_389;
}
case 6:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_1);
x_390 = lean_ctor_get(x_234, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_234, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_234, 2);
lean_inc(x_392);
x_393 = lean_ctor_get_uint8(x_234, sizeof(void*)*3 + 8);
lean_dec(x_234);
x_394 = l_Lean_Expr_lam___override(x_390, x_391, x_392, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_235);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_233);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_397, x_2, x_3, x_223);
lean_dec(x_397);
return x_398;
}
case 7:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_1);
x_399 = lean_ctor_get(x_234, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_234, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_234, 2);
lean_inc(x_401);
x_402 = lean_ctor_get_uint8(x_234, sizeof(void*)*3 + 8);
lean_dec(x_234);
x_403 = l_Lean_Expr_forallE___override(x_399, x_400, x_401, x_402);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_235);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_233);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_406, x_2, x_3, x_223);
lean_dec(x_406);
return x_407;
}
case 8:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_1);
x_408 = lean_ctor_get(x_234, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_234, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_234, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_234, 3);
lean_inc(x_411);
x_412 = lean_ctor_get_uint8(x_234, sizeof(void*)*4 + 8);
lean_dec(x_234);
x_413 = l_Lean_Expr_letE___override(x_408, x_409, x_410, x_411, x_412);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_235);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_233);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_415);
x_417 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_416, x_2, x_3, x_223);
lean_dec(x_416);
return x_417;
}
case 9:
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_1);
x_418 = lean_ctor_get(x_234, 0);
lean_inc(x_418);
lean_dec(x_234);
x_419 = l_Lean_Expr_lit___override(x_418);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_235);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_233);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_422, x_2, x_3, x_223);
lean_dec(x_422);
return x_423;
}
case 10:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_1);
x_424 = lean_ctor_get(x_234, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_234, 1);
lean_inc(x_425);
lean_dec(x_234);
x_426 = l_Lean_Expr_mdata___override(x_424, x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_235);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_233);
lean_ctor_set(x_428, 1, x_427);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_430 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_429, x_2, x_3, x_223);
lean_dec(x_429);
return x_430;
}
default: 
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_1);
x_431 = lean_ctor_get(x_234, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_234, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_234, 2);
lean_inc(x_433);
lean_dec(x_234);
x_434 = l_Lean_Expr_proj___override(x_431, x_432, x_433);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_235);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_233);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_436);
x_438 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_437, x_2, x_3, x_223);
lean_dec(x_437);
return x_438;
}
}
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_5);
if (x_439 == 0)
{
return x_5;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_5, 0);
x_441 = lean_ctor_get(x_5, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_5);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_4, 6);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_ScopedEnvExtension_addCore___redArg(x_12, x_1, x_2, x_3, x_11);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 3);
lean_inc(x_16);
x_17 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_18);
lean_ctor_set(x_7, 1, x_18);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_ctor_get(x_9, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 7);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_7);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_st_ref_set(x_5, x_22, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_ctor_get(x_4, 6);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = l_Lean_ScopedEnvExtension_addCore___redArg(x_33, x_1, x_2, x_3, x_32);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 3);
lean_inc(x_37);
x_38 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_30, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 7);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_41);
lean_ctor_set(x_44, 6, x_42);
lean_ctor_set(x_44, 7, x_43);
x_45 = lean_st_ref_set(x_5, x_44, x_31);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_mk_string_unchecked("invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported.", 102, 102);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_10, x_3, x_4, x_8);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Lean_Compiler_CSimp_ext;
x_15 = l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg(x_14, x_13, x_2, x_3, x_4, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___redArg(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_ScopedEnvExtension_add___at___Lean_Compiler_CSimp_add_spec__0(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Compiler_CSimp_add(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_CSimp_add(x_1, x_3, x_4, x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
return x_9;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Compiler", 8, 8);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("CSimp", 5, 5);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_5);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = lean_mk_string_unchecked("CSimpAttr", 9, 9);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(471u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("csimp", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("simplification theorem for the compiler", 39, 39);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_3);
x_30 = l_Lean_registerBuiltinAttribute(x_29, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_CSimp_initFn___lam__0____x40_Lean_Compiler_CSimpAttr___hyg_471_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_CSimp_initFn___lam__1____x40_Lean_Compiler_CSimpAttr___hyg_471_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Expr_constName_x21(x_2);
x_7 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_box(0), x_5, x_6);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_Expr_constLevels_x21(x_2);
x_12 = l_Lean_Expr_const___override(x_10, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Lean_Expr_constLevels_x21(x_2);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Compiler_CSimp_instInhabitedState;
x_4 = l_Lean_Compiler_CSimp_ext;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_8 = l_Lean_ScopedEnvExtension_getState___redArg(x_3, x_4, x_1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_replaceConstants___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_replace_expr(x_9, x_2);
lean_dec(x_2);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_CSimp_replaceConstants___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasCSimpAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_Compiler_CSimp_instInhabitedState;
x_4 = l_Lean_Compiler_CSimp_ext;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_8 = l_Lean_ScopedEnvExtension_getState___redArg(x_3, x_4, x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_9, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasCSimpAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasCSimpAttribute(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_CSimp_instInhabitedEntry = _init_l_Lean_Compiler_CSimp_instInhabitedEntry();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedEntry);
l_Lean_Compiler_CSimp_instInhabitedState = _init_l_Lean_Compiler_CSimp_instInhabitedState();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState);
if (builtin) {res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_137_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_CSimp_ext = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_CSimp_ext);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_471_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
