// Lean compiler output
// Module: Lean.Compiler.IR.ToIRType
// Imports: Lean.Environment Lean.Compiler.IR.Format Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.Types
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
static lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_instInhabitedCtorLayout___closed__0;
static lean_object* l_Lean_IR_getCtorLayout___closed__0;
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_toIRType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__5;
static lean_object* l_panic___at___Lean_IR_toIRType_spec__0___closed__0;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__4;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__2;
static lean_object* l_Lean_IR_toIRType___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedCtorFieldInfo;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__23;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__3;
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__5;
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4;
static lean_object* l_Lean_IR_toIRType___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__4;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__13;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__18;
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2;
static lean_object* l_Lean_IR_toIRType___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__1;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__3;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__6;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__12;
static lean_object* l_Lean_IR_CtorFieldInfo_instToFormat___closed__0;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__24;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__11;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__9;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__16;
static lean_object* l_Lean_IR_toIRType___closed__7;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_lowerEnumToScalarType_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__10;
static lean_object* l_Lean_IR_instInhabitedCtorLayout___closed__2;
lean_object* l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__14;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__8;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_scalarTypeExt;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_ctorLayoutExt;
static lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__26;
LEAN_EXPORT lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedCtorLayout;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__17;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__2;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__15;
static uint64_t l_Lean_IR_getCtorLayout_fillCache___closed__21;
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1;
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__8;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__27;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_5_(lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__6;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__10;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__9;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__25;
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__22;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_instToFormat;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_lowerEnumToScalarType_x3f___closed__0;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__13;
static lean_object* l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_999_(lean_object*);
static lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__0;
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__19;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__1;
static lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instInhabitedCtorLayout___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__20;
static lean_object* l_Lean_IR_toIRType___closed__2;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIRType___closed__3;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__0;
static lean_object* l_Lean_IR_toIRType___closed__11;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__5;
static lean_object* l_Lean_IR_getCtorLayout_fillCache___closed__11;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIRType", 25, 25);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.lowerEnumToScalarType\?.fillCache", 40, 40);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected valid constructor name", 31, 31);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(34u);
x_4 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
lean_inc(x_2);
x_27 = l_Lean_Environment_find_x3f(x_2, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_free_object(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_24;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 6)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Expr_isForall(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_free_object(x_4);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_12;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4;
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
lean_dec(x_28);
lean_free_object(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_24;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3;
x_17 = l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(x_16, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_12;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_7 = x_18;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
lean_inc(x_2);
x_52 = l_Lean_Environment_find_x3f(x_2, x_36, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_inc(x_7);
lean_inc(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = x_8;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 6)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Expr_isForall(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_inc(x_1);
{
lean_object* _tmp_3 = x_37;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_8);
return x_61;
}
}
else
{
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = x_8;
goto block_49;
}
}
block_49:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3;
x_42 = l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(x_41, x_38, x_39, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_37;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_7 = x_43;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_lowerEnumToScalarType_x3f_fillCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_12);
x_15 = l_Lean_Environment_find_x3f(x_12, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_11;
goto block_8;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0;
lean_inc(x_18);
x_21 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg(x_20, x_12, x_19, x_18, x_20, x_2, x_3, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = l_List_lengthTR___redArg(x_18);
lean_dec(x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(256u);
x_30 = lean_nat_dec_lt(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(65536u);
x_32 = lean_nat_dec_lt(x_26, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_cstr_to_nat("4294967296");
x_34 = lean_nat_dec_lt(x_26, x_33);
lean_dec(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1;
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
}
else
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2;
lean_ctor_set(x_21, 0, x_37);
return x_21;
}
}
else
{
lean_object* x_38; 
lean_dec(x_26);
x_38 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3;
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; 
lean_dec(x_26);
x_39 = lean_box(0);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = l_List_lengthTR___redArg(x_18);
lean_dec(x_18);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(256u);
x_45 = lean_nat_dec_lt(x_41, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(65536u);
x_47 = lean_nat_dec_lt(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_cstr_to_nat("4294967296");
x_49 = lean_nat_dec_lt(x_41, x_48);
lean_dec(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_41);
x_54 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
x_56 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_40);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_18);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_21, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_23, 0);
lean_inc(x_62);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_62);
return x_21;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_ctor_get(x_23, 0);
lean_inc(x_64);
lean_dec(x_23);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_18);
x_66 = !lean_is_exclusive(x_21);
if (x_66 == 0)
{
return x_21;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_21, 0);
x_68 = lean_ctor_get(x_21, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_21);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_11;
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_lowerEnumToScalarType_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_scalarTypeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_lowerEnumToScalarType_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_lowerEnumToScalarType_x3f___closed__0;
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(x_5, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_IR_lowerEnumToScalarType_x3f_fillCache(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(x_5, x_1, x_10, x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_IR_toIRType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_toIRType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___Lean_IR_toIRType_spec__0___closed__0;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt64", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("USize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float32", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.toIRType", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid type", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_toIRType___closed__10;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(74u);
x_4 = l_Lean_IR_toIRType___closed__9;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
x_34 = l_Lean_IR_toIRType___closed__0;
x_35 = lean_string_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_IR_toIRType___closed__1;
x_37 = lean_string_dec_eq(x_33, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_IR_toIRType___closed__2;
x_39 = lean_string_dec_eq(x_33, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_IR_toIRType___closed__3;
x_41 = lean_string_dec_eq(x_33, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_IR_toIRType___closed__4;
x_43 = lean_string_dec_eq(x_33, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_IR_toIRType___closed__5;
x_45 = lean_string_dec_eq(x_33, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_IR_toIRType___closed__6;
x_47 = lean_string_dec_eq(x_33, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_IR_toIRType___closed__7;
x_49 = lean_string_dec_eq(x_33, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_IR_toIRType___closed__8;
x_51 = lean_string_dec_eq(x_33, x_50);
lean_dec(x_33);
if (x_51 == 0)
{
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
goto block_31;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(6);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(4);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_4);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
}
else
{
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_4;
goto block_8;
}
}
else
{
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_4;
goto block_8;
}
}
else
{
lean_dec(x_32);
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
goto block_31;
}
}
else
{
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
goto block_31;
}
block_31:
{
lean_object* x_13; 
x_13 = l_Lean_IR_lowerEnumToScalarType_x3f(x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(7);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
case 5:
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
if (lean_obj_tag(x_66) == 4)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_IR_lowerEnumToScalarType_x3f(x_67, x_2, x_3, x_4);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = lean_box(7);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_box(7);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_68, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_dec(x_69);
lean_ctor_set(x_68, 0, x_78);
return x_68;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_dec(x_68);
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_68);
if (x_82 == 0)
{
return x_68;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_68, 0);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_68);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(7);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_4);
return x_87;
}
}
case 7:
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_box(7);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
default: 
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_90 = l_Lean_IR_toIRType___closed__11;
x_91 = l_panic___at___Lean_IR_toIRType_spec__0(x_90, x_2, x_3, x_4);
return x_91;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("◾", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("obj@", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usize@", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scalar#", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_CtorFieldInfo_format___closed__1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_CtorFieldInfo_format___closed__3;
x_6 = l_Nat_reprFast(x_4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_IR_CtorFieldInfo_format___closed__3;
x_12 = l_Nat_reprFast(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = l_Lean_IR_CtorFieldInfo_format___closed__7;
x_20 = l_Nat_reprFast(x_18);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_IR_CtorFieldInfo_format___closed__7;
x_26 = l_Nat_reprFast(x_24);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l_Lean_IR_CtorFieldInfo_format___closed__9;
x_35 = l_Nat_reprFast(x_31);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_IR_CtorFieldInfo_format___closed__11;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Nat_reprFast(x_32);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_IR_CtorFieldInfo_format___closed__13;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_33);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CtorFieldInfo_instToFormat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorLayout___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorLayout___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorLayout___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_instInhabitedCtorLayout___closed__1;
x_2 = l_Lean_IR_instInhabitedCtorLayout___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorLayout() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedCtorLayout___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_999_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedCtorLayout;
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_4, x_3, x_9);
switch (lean_obj_tag(x_8)) {
case 0:
{
x_11 = x_8;
x_12 = x_5;
goto block_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_18, x_1);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_8;
x_12 = x_5;
goto block_17;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_25 = lean_nat_add(x_5, x_18);
lean_ctor_set(x_8, 1, x_5);
x_11 = x_8;
x_12 = x_25;
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_26 = lean_nat_add(x_5, x_18);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_19);
x_11 = x_27;
x_12 = x_26;
goto block_17;
}
}
}
default: 
{
x_11 = x_8;
x_12 = x_5;
goto block_17;
}
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_10, x_3, x_11);
x_3 = x_14;
x_4 = x_15;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___Lean_IR_toIRType_spec__0___closed__0;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.getCtorLayout.fillCache", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(148u);
x_4 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_33; 
x_33 = lean_usize_dec_lt(x_4, x_3);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_array_uget(x_35, x_4);
x_37 = l_Lean_Expr_fvarId_x21(x_36);
lean_dec(x_36);
lean_inc(x_6);
x_38 = l_Lean_FVarId_getType___redArg(x_37, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Compiler_LCNF_toLCNFType(x_39, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
x_44 = l_Lean_Compiler_LCNF_toMonoType(x_42, x_8, x_9, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_IR_toIRType(x_45, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
switch (lean_obj_tag(x_52)) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_dec(x_5);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_unsigned_to_nat(8u);
lean_inc(x_1);
x_60 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_52);
x_61 = lean_unbox(x_55);
lean_dec(x_55);
x_62 = lean_unbox(x_56);
lean_dec(x_56);
x_63 = lean_unbox(x_57);
lean_dec(x_57);
x_11 = x_54;
x_12 = x_61;
x_13 = x_62;
x_14 = x_63;
x_15 = x_33;
x_16 = x_58;
x_17 = x_60;
x_18 = x_53;
goto block_32;
}
case 1:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; 
lean_dec(x_48);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_ctor_get(x_5, 0);
lean_inc(x_65);
lean_dec(x_5);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_ctor_get(x_50, 0);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_ctor_get(x_51, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_dec(x_51);
x_70 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_71 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_1);
lean_ctor_set(x_71, 2, x_52);
x_72 = lean_unbox(x_66);
lean_dec(x_66);
x_73 = lean_unbox(x_67);
lean_dec(x_67);
x_74 = lean_unbox(x_68);
lean_dec(x_68);
x_11 = x_65;
x_12 = x_33;
x_13 = x_72;
x_14 = x_73;
x_15 = x_74;
x_16 = x_69;
x_17 = x_71;
x_18 = x_64;
goto block_32;
}
case 2:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; 
lean_dec(x_49);
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = lean_ctor_get(x_5, 0);
lean_inc(x_76);
lean_dec(x_5);
x_77 = lean_ctor_get(x_48, 0);
lean_inc(x_77);
lean_dec(x_48);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
lean_dec(x_50);
x_79 = lean_ctor_get(x_51, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_dec(x_51);
x_81 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_82 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_1);
lean_ctor_set(x_82, 2, x_52);
x_83 = lean_unbox(x_77);
lean_dec(x_77);
x_84 = lean_unbox(x_78);
lean_dec(x_78);
x_85 = lean_unbox(x_79);
lean_dec(x_79);
x_11 = x_76;
x_12 = x_83;
x_13 = x_33;
x_14 = x_84;
x_15 = x_85;
x_16 = x_80;
x_17 = x_82;
x_18 = x_75;
goto block_32;
}
case 3:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; 
lean_dec(x_50);
x_86 = lean_ctor_get(x_47, 1);
lean_inc(x_86);
lean_dec(x_47);
x_87 = lean_ctor_get(x_5, 0);
lean_inc(x_87);
lean_dec(x_5);
x_88 = lean_ctor_get(x_48, 0);
lean_inc(x_88);
lean_dec(x_48);
x_89 = lean_ctor_get(x_49, 0);
lean_inc(x_89);
lean_dec(x_49);
x_90 = lean_ctor_get(x_51, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_51, 1);
lean_inc(x_91);
lean_dec(x_51);
x_92 = lean_unsigned_to_nat(4u);
lean_inc(x_1);
x_93 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_1);
lean_ctor_set(x_93, 2, x_52);
x_94 = lean_unbox(x_88);
lean_dec(x_88);
x_95 = lean_unbox(x_89);
lean_dec(x_89);
x_96 = lean_unbox(x_90);
lean_dec(x_90);
x_11 = x_87;
x_12 = x_94;
x_13 = x_95;
x_14 = x_33;
x_15 = x_96;
x_16 = x_91;
x_17 = x_93;
x_18 = x_86;
goto block_32;
}
case 4:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; 
x_97 = lean_ctor_get(x_47, 1);
lean_inc(x_97);
lean_dec(x_47);
x_98 = lean_ctor_get(x_5, 0);
lean_inc(x_98);
lean_dec(x_5);
x_99 = lean_ctor_get(x_48, 0);
lean_inc(x_99);
lean_dec(x_48);
x_100 = lean_ctor_get(x_49, 0);
lean_inc(x_100);
lean_dec(x_49);
x_101 = lean_ctor_get(x_50, 0);
lean_inc(x_101);
lean_dec(x_50);
x_102 = lean_ctor_get(x_51, 1);
lean_inc(x_102);
lean_dec(x_51);
x_103 = lean_unsigned_to_nat(8u);
lean_inc(x_1);
x_104 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_1);
lean_ctor_set(x_104, 2, x_52);
x_105 = lean_unbox(x_99);
lean_dec(x_99);
x_106 = lean_unbox(x_100);
lean_dec(x_100);
x_107 = lean_unbox(x_101);
lean_dec(x_101);
x_11 = x_98;
x_12 = x_105;
x_13 = x_106;
x_14 = x_107;
x_15 = x_33;
x_16 = x_102;
x_17 = x_104;
x_18 = x_97;
goto block_32;
}
case 5:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; 
x_108 = lean_ctor_get(x_47, 1);
lean_inc(x_108);
lean_dec(x_47);
x_109 = lean_ctor_get(x_5, 0);
lean_inc(x_109);
lean_dec(x_5);
x_110 = lean_ctor_get(x_48, 0);
lean_inc(x_110);
lean_dec(x_48);
x_111 = lean_ctor_get(x_49, 0);
lean_inc(x_111);
lean_dec(x_49);
x_112 = lean_ctor_get(x_50, 0);
lean_inc(x_112);
lean_dec(x_50);
x_113 = lean_ctor_get(x_51, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_51, 1);
lean_inc(x_114);
lean_dec(x_51);
lean_inc(x_1);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_1);
x_116 = lean_unbox(x_110);
lean_dec(x_110);
x_117 = lean_unbox(x_111);
lean_dec(x_111);
x_118 = lean_unbox(x_112);
lean_dec(x_112);
x_119 = lean_unbox(x_113);
lean_dec(x_113);
x_11 = x_109;
x_12 = x_116;
x_13 = x_117;
x_14 = x_118;
x_15 = x_119;
x_16 = x_114;
x_17 = x_115;
x_18 = x_108;
goto block_32;
}
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; 
x_120 = lean_ctor_get(x_47, 1);
lean_inc(x_120);
lean_dec(x_47);
x_121 = lean_ctor_get(x_5, 0);
lean_inc(x_121);
lean_dec(x_5);
x_122 = lean_ctor_get(x_48, 0);
lean_inc(x_122);
lean_dec(x_48);
x_123 = lean_ctor_get(x_49, 0);
lean_inc(x_123);
lean_dec(x_49);
x_124 = lean_ctor_get(x_50, 0);
lean_inc(x_124);
lean_dec(x_50);
x_125 = lean_ctor_get(x_51, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_51, 1);
lean_inc(x_126);
lean_dec(x_51);
x_127 = lean_box(0);
x_128 = lean_unbox(x_122);
lean_dec(x_122);
x_129 = lean_unbox(x_123);
lean_dec(x_123);
x_130 = lean_unbox(x_124);
lean_dec(x_124);
x_131 = lean_unbox(x_125);
lean_dec(x_125);
x_11 = x_121;
x_12 = x_128;
x_13 = x_129;
x_14 = x_130;
x_15 = x_131;
x_16 = x_126;
x_17 = x_127;
x_18 = x_120;
goto block_32;
}
case 9:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; 
lean_dec(x_50);
x_132 = lean_ctor_get(x_47, 1);
lean_inc(x_132);
lean_dec(x_47);
x_133 = lean_ctor_get(x_5, 0);
lean_inc(x_133);
lean_dec(x_5);
x_134 = lean_ctor_get(x_48, 0);
lean_inc(x_134);
lean_dec(x_48);
x_135 = lean_ctor_get(x_49, 0);
lean_inc(x_135);
lean_dec(x_49);
x_136 = lean_ctor_get(x_51, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_51, 1);
lean_inc(x_137);
lean_dec(x_51);
x_138 = lean_unsigned_to_nat(4u);
lean_inc(x_1);
x_139 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_1);
lean_ctor_set(x_139, 2, x_52);
x_140 = lean_unbox(x_134);
lean_dec(x_134);
x_141 = lean_unbox(x_135);
lean_dec(x_135);
x_142 = lean_unbox(x_136);
lean_dec(x_136);
x_11 = x_133;
x_12 = x_140;
x_13 = x_141;
x_14 = x_33;
x_15 = x_142;
x_16 = x_137;
x_17 = x_139;
x_18 = x_132;
goto block_32;
}
case 10:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_52);
x_143 = lean_ctor_get(x_47, 1);
lean_inc(x_143);
lean_dec(x_47);
x_144 = lean_ctor_get(x_5, 0);
lean_inc(x_144);
lean_dec(x_5);
x_145 = lean_ctor_get(x_48, 0);
lean_inc(x_145);
lean_dec(x_48);
x_146 = lean_ctor_get(x_49, 0);
lean_inc(x_146);
lean_dec(x_49);
x_147 = lean_ctor_get(x_50, 0);
lean_inc(x_147);
lean_dec(x_50);
x_148 = lean_ctor_get(x_51, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_51, 1);
lean_inc(x_149);
lean_dec(x_51);
x_150 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_151 = l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2(x_150, x_6, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_145);
lean_dec(x_145);
x_155 = lean_unbox(x_146);
lean_dec(x_146);
x_156 = lean_unbox(x_147);
lean_dec(x_147);
x_157 = lean_unbox(x_148);
lean_dec(x_148);
x_11 = x_144;
x_12 = x_154;
x_13 = x_155;
x_14 = x_156;
x_15 = x_157;
x_16 = x_149;
x_17 = x_152;
x_18 = x_153;
goto block_32;
}
else
{
uint8_t x_158; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_151);
if (x_158 == 0)
{
return x_151;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_151, 0);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_151);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
case 11:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_52);
x_162 = lean_ctor_get(x_47, 1);
lean_inc(x_162);
lean_dec(x_47);
x_163 = lean_ctor_get(x_5, 0);
lean_inc(x_163);
lean_dec(x_5);
x_164 = lean_ctor_get(x_48, 0);
lean_inc(x_164);
lean_dec(x_48);
x_165 = lean_ctor_get(x_49, 0);
lean_inc(x_165);
lean_dec(x_49);
x_166 = lean_ctor_get(x_50, 0);
lean_inc(x_166);
lean_dec(x_50);
x_167 = lean_ctor_get(x_51, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_51, 1);
lean_inc(x_168);
lean_dec(x_51);
x_169 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_170 = l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2(x_169, x_6, x_7, x_8, x_9, x_162);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unbox(x_164);
lean_dec(x_164);
x_174 = lean_unbox(x_165);
lean_dec(x_165);
x_175 = lean_unbox(x_166);
lean_dec(x_166);
x_176 = lean_unbox(x_167);
lean_dec(x_167);
x_11 = x_163;
x_12 = x_173;
x_13 = x_174;
x_14 = x_175;
x_15 = x_176;
x_16 = x_168;
x_17 = x_171;
x_18 = x_172;
goto block_32;
}
else
{
uint8_t x_177; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_170);
if (x_177 == 0)
{
return x_170;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_170, 0);
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_170);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
default: 
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; 
lean_dec(x_52);
x_181 = lean_ctor_get(x_47, 1);
lean_inc(x_181);
lean_dec(x_47);
x_182 = lean_ctor_get(x_5, 0);
lean_inc(x_182);
lean_dec(x_5);
x_183 = lean_ctor_get(x_48, 0);
lean_inc(x_183);
lean_dec(x_48);
x_184 = lean_ctor_get(x_49, 0);
lean_inc(x_184);
lean_dec(x_49);
x_185 = lean_ctor_get(x_50, 0);
lean_inc(x_185);
lean_dec(x_50);
x_186 = lean_ctor_get(x_51, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_51, 1);
lean_inc(x_187);
lean_dec(x_51);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_add(x_187, x_188);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_187);
x_191 = lean_unbox(x_183);
lean_dec(x_183);
x_192 = lean_unbox(x_184);
lean_dec(x_184);
x_193 = lean_unbox(x_185);
lean_dec(x_185);
x_194 = lean_unbox(x_186);
lean_dec(x_186);
x_11 = x_182;
x_12 = x_191;
x_13 = x_192;
x_14 = x_193;
x_15 = x_194;
x_16 = x_189;
x_17 = x_190;
x_18 = x_181;
goto block_32;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_47);
if (x_195 == 0)
{
return x_47;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_47, 0);
x_197 = lean_ctor_get(x_47, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_47);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_44);
if (x_199 == 0)
{
return x_44;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_44, 0);
x_201 = lean_ctor_get(x_44, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_44);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_41);
if (x_203 == 0)
{
return x_41;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_41, 0);
x_205 = lean_ctor_get(x_41, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_41);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_38);
if (x_207 == 0)
{
return x_38;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_38, 0);
x_209 = lean_ctor_get(x_38, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_38);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
block_32:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_19 = lean_array_push(x_11, x_17);
x_20 = lean_box(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_box(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_box(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_box(x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_4, x_29);
x_4 = x_30;
x_5 = x_28;
x_10 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
switch (lean_obj_tag(x_7)) {
case 0:
{
x_10 = x_7;
x_11 = x_4;
goto block_16;
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_ctor_set(x_7, 0, x_4);
x_10 = x_7;
x_11 = x_20;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_4);
x_10 = x_23;
x_11 = x_22;
goto block_16;
}
}
default: 
{
x_10 = x_7;
x_11 = x_4;
goto block_16;
}
}
block_16:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0(x_2, x_4, x_5, x_1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_117; 
x_59 = lean_mk_empty_array_with_capacity(x_4);
x_60 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_add(x_6, x_4);
x_113 = lean_array_get_size(x_7);
x_117 = lean_nat_dec_le(x_6, x_60);
if (x_117 == 0)
{
x_114 = x_6;
goto block_116;
}
else
{
lean_dec(x_6);
x_114 = x_60;
goto block_116;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
block_33:
{
if (x_24 == 0)
{
lean_dec(x_3);
x_14 = x_23;
x_15 = x_25;
x_16 = x_26;
x_17 = x_27;
x_18 = x_28;
goto block_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_apply_3(x_3, x_26, x_29, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_14 = x_23;
x_15 = x_25;
x_16 = x_31;
x_17 = x_32;
x_18 = x_28;
goto block_22;
}
}
block_45:
{
if (x_36 == 0)
{
x_23 = x_35;
x_24 = x_34;
x_25 = x_37;
x_26 = x_38;
x_27 = x_39;
x_28 = x_40;
goto block_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_unsigned_to_nat(2u);
lean_inc(x_3);
x_42 = lean_apply_3(x_3, x_38, x_41, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_23 = x_35;
x_24 = x_34;
x_25 = x_37;
x_26 = x_43;
x_27 = x_44;
x_28 = x_40;
goto block_33;
}
}
block_58:
{
if (x_49 == 0)
{
x_34 = x_48;
x_35 = x_47;
x_36 = x_46;
x_37 = x_50;
x_38 = x_51;
x_39 = x_52;
x_40 = x_53;
goto block_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_unsigned_to_nat(4u);
lean_inc(x_3);
x_55 = lean_apply_3(x_3, x_51, x_54, x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_34 = x_48;
x_35 = x_47;
x_36 = x_46;
x_37 = x_50;
x_38 = x_56;
x_39 = x_57;
x_40 = x_53;
goto block_45;
}
}
block_111:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_63 = l_Array_toSubarray___redArg(x_7, x_61, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_box(x_5);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
x_68 = lean_box(x_5);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box(x_5);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_box(x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_59);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_76 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_77 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3(x_60, x_63, x_75, x_76, x_74, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
lean_dec(x_80);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_array_size(x_84);
x_91 = 0;
lean_inc(x_89);
x_92 = l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4(x_90, x_91, x_84, x_89);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_nat_sub(x_94, x_89);
lean_dec(x_94);
x_96 = lean_unbox(x_88);
lean_dec(x_88);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; uint8_t x_99; 
x_97 = lean_unbox(x_86);
lean_dec(x_86);
x_98 = lean_unbox(x_85);
lean_dec(x_85);
x_99 = lean_unbox(x_87);
lean_dec(x_87);
x_46 = x_97;
x_47 = x_95;
x_48 = x_98;
x_49 = x_99;
x_50 = x_89;
x_51 = x_93;
x_52 = x_60;
x_53 = x_83;
goto block_58;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; 
x_100 = lean_unsigned_to_nat(8u);
lean_inc(x_3);
x_101 = lean_apply_3(x_3, x_93, x_100, x_60);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_unbox(x_86);
lean_dec(x_86);
x_105 = lean_unbox(x_85);
lean_dec(x_85);
x_106 = lean_unbox(x_87);
lean_dec(x_87);
x_46 = x_104;
x_47 = x_95;
x_48 = x_105;
x_49 = x_106;
x_50 = x_89;
x_51 = x_102;
x_52 = x_103;
x_53 = x_83;
goto block_58;
}
}
else
{
uint8_t x_107; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_77);
if (x_107 == 0)
{
return x_77;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_77, 0);
x_109 = lean_ctor_get(x_77, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_77);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
block_116:
{
uint8_t x_115; 
x_115 = lean_nat_dec_le(x_112, x_113);
if (x_115 == 0)
{
lean_dec(x_112);
x_61 = x_114;
x_62 = x_113;
goto block_111;
}
else
{
lean_dec(x_113);
x_61 = x_114;
x_62 = x_112;
goto block_111;
}
}
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1;
x_2 = lean_unsigned_to_nat(64u);
x_3 = lean_unsigned_to_nat(111u);
x_4 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__7;
x_2 = l_Lean_IR_getCtorLayout_fillCache___closed__6;
x_3 = l_Lean_IR_getCtorLayout_fillCache___closed__5;
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__4;
x_5 = l_Lean_IR_getCtorLayout_fillCache___closed__3;
x_6 = l_Lean_IR_getCtorLayout_fillCache___closed__2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__12;
x_2 = l_Lean_IR_getCtorLayout_fillCache___closed__11;
x_3 = l_Lean_IR_getCtorLayout_fillCache___closed__10;
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__9;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__16() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_getCtorLayout_fillCache___closed__14;
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__15;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__17;
x_2 = l_Lean_IR_getCtorLayout_fillCache___closed__2;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__18;
x_2 = l_Lean_IR_getCtorLayout_fillCache___closed__16;
x_3 = lean_box(0);
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__13;
x_5 = l_Lean_IR_getCtorLayout_fillCache___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 19);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
x_25 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 18, x_25);
return x_6;
}
}
static uint64_t _init_l_Lean_IR_getCtorLayout_fillCache___closed__21() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__20;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_getCtorLayout_fillCache___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__24() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_getCtorLayout_fillCache___closed__14;
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__23;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_getCtorLayout_fillCache___closed__24;
x_3 = l_Lean_IR_getCtorLayout_fillCache___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout_fillCache___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_IR_getCtorLayout_fillCache___closed__26;
x_5 = l_Lean_IR_getCtorLayout_fillCache___closed__25;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_IR_getCtorLayout_fillCache___closed__21;
x_9 = l_Lean_IR_getCtorLayout_fillCache___closed__20;
x_10 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_2);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*7, x_8);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 8, x_11);
x_12 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 9, x_12);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 10, x_13);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_st_ref_get(x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
lean_inc(x_1);
x_17 = l_Lean_Environment_find_x3f(x_14, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_1);
x_5 = x_2;
x_6 = x_3;
x_7 = x_13;
goto block_10;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_IR_getCtorLayout_fillCache___closed__19;
x_21 = lean_st_mk_ref(x_20, x_13);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 4);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_closure((void*)(l_Lean_IR_getCtorLayout_fillCache___lam__0___boxed), 3, 0);
x_30 = lean_alloc_closure((void*)(l_Lean_IR_getCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_25);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_15);
lean_closure_set(x_30, 5, x_26);
x_31 = l_Lean_IR_getCtorLayout_fillCache___closed__27;
x_32 = lean_unbox(x_15);
x_33 = lean_unbox(x_15);
lean_inc(x_23);
x_34 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_28, x_30, x_32, x_33, x_31, x_23, x_2, x_3, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_23, x_36);
lean_dec(x_23);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_dec(x_23);
return x_34;
}
}
else
{
lean_dec(x_18);
lean_dec(x_1);
x_5 = x_2;
x_6 = x_3;
x_7 = x_13;
goto block_10;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_getCtorLayout_fillCache___closed__0;
x_9 = l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__1(x_8, x_5, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_getCtorLayout_fillCache_spec__4(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getCtorLayout_fillCache___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout_fillCache___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_IR_getCtorLayout_fillCache___lam__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_IR_getCtorLayout___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ctorLayoutExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_getCtorLayout___closed__0;
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(x_5, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_IR_getCtorLayout_fillCache(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(x_5, x_1, x_10, x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_scalarTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_scalarTypeExt);
lean_dec_ref(res);
}l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__0);
l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__1);
l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__2);
l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__3);
l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_lowerEnumToScalarType_x3f_fillCache_spec__0___redArg___closed__4);
l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0 = _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0();
lean_mark_persistent(l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__0);
l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1 = _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1();
lean_mark_persistent(l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__1);
l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2 = _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2();
lean_mark_persistent(l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__2);
l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3 = _init_l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3();
lean_mark_persistent(l_Lean_IR_lowerEnumToScalarType_x3f_fillCache___closed__3);
l_Lean_IR_lowerEnumToScalarType_x3f___closed__0 = _init_l_Lean_IR_lowerEnumToScalarType_x3f___closed__0();
lean_mark_persistent(l_Lean_IR_lowerEnumToScalarType_x3f___closed__0);
l_panic___at___Lean_IR_toIRType_spec__0___closed__0 = _init_l_panic___at___Lean_IR_toIRType_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_toIRType_spec__0___closed__0);
l_Lean_IR_toIRType___closed__0 = _init_l_Lean_IR_toIRType___closed__0();
lean_mark_persistent(l_Lean_IR_toIRType___closed__0);
l_Lean_IR_toIRType___closed__1 = _init_l_Lean_IR_toIRType___closed__1();
lean_mark_persistent(l_Lean_IR_toIRType___closed__1);
l_Lean_IR_toIRType___closed__2 = _init_l_Lean_IR_toIRType___closed__2();
lean_mark_persistent(l_Lean_IR_toIRType___closed__2);
l_Lean_IR_toIRType___closed__3 = _init_l_Lean_IR_toIRType___closed__3();
lean_mark_persistent(l_Lean_IR_toIRType___closed__3);
l_Lean_IR_toIRType___closed__4 = _init_l_Lean_IR_toIRType___closed__4();
lean_mark_persistent(l_Lean_IR_toIRType___closed__4);
l_Lean_IR_toIRType___closed__5 = _init_l_Lean_IR_toIRType___closed__5();
lean_mark_persistent(l_Lean_IR_toIRType___closed__5);
l_Lean_IR_toIRType___closed__6 = _init_l_Lean_IR_toIRType___closed__6();
lean_mark_persistent(l_Lean_IR_toIRType___closed__6);
l_Lean_IR_toIRType___closed__7 = _init_l_Lean_IR_toIRType___closed__7();
lean_mark_persistent(l_Lean_IR_toIRType___closed__7);
l_Lean_IR_toIRType___closed__8 = _init_l_Lean_IR_toIRType___closed__8();
lean_mark_persistent(l_Lean_IR_toIRType___closed__8);
l_Lean_IR_toIRType___closed__9 = _init_l_Lean_IR_toIRType___closed__9();
lean_mark_persistent(l_Lean_IR_toIRType___closed__9);
l_Lean_IR_toIRType___closed__10 = _init_l_Lean_IR_toIRType___closed__10();
lean_mark_persistent(l_Lean_IR_toIRType___closed__10);
l_Lean_IR_toIRType___closed__11 = _init_l_Lean_IR_toIRType___closed__11();
lean_mark_persistent(l_Lean_IR_toIRType___closed__11);
l_Lean_IR_instInhabitedCtorFieldInfo = _init_l_Lean_IR_instInhabitedCtorFieldInfo();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorFieldInfo);
l_Lean_IR_CtorFieldInfo_format___closed__0 = _init_l_Lean_IR_CtorFieldInfo_format___closed__0();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__0);
l_Lean_IR_CtorFieldInfo_format___closed__1 = _init_l_Lean_IR_CtorFieldInfo_format___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__1);
l_Lean_IR_CtorFieldInfo_format___closed__2 = _init_l_Lean_IR_CtorFieldInfo_format___closed__2();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__2);
l_Lean_IR_CtorFieldInfo_format___closed__3 = _init_l_Lean_IR_CtorFieldInfo_format___closed__3();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__3);
l_Lean_IR_CtorFieldInfo_format___closed__4 = _init_l_Lean_IR_CtorFieldInfo_format___closed__4();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__4);
l_Lean_IR_CtorFieldInfo_format___closed__5 = _init_l_Lean_IR_CtorFieldInfo_format___closed__5();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__5);
l_Lean_IR_CtorFieldInfo_format___closed__6 = _init_l_Lean_IR_CtorFieldInfo_format___closed__6();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__6);
l_Lean_IR_CtorFieldInfo_format___closed__7 = _init_l_Lean_IR_CtorFieldInfo_format___closed__7();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__7);
l_Lean_IR_CtorFieldInfo_format___closed__8 = _init_l_Lean_IR_CtorFieldInfo_format___closed__8();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__8);
l_Lean_IR_CtorFieldInfo_format___closed__9 = _init_l_Lean_IR_CtorFieldInfo_format___closed__9();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__9);
l_Lean_IR_CtorFieldInfo_format___closed__10 = _init_l_Lean_IR_CtorFieldInfo_format___closed__10();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__10);
l_Lean_IR_CtorFieldInfo_format___closed__11 = _init_l_Lean_IR_CtorFieldInfo_format___closed__11();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__11);
l_Lean_IR_CtorFieldInfo_format___closed__12 = _init_l_Lean_IR_CtorFieldInfo_format___closed__12();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__12);
l_Lean_IR_CtorFieldInfo_format___closed__13 = _init_l_Lean_IR_CtorFieldInfo_format___closed__13();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__13);
l_Lean_IR_CtorFieldInfo_instToFormat___closed__0 = _init_l_Lean_IR_CtorFieldInfo_instToFormat___closed__0();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormat___closed__0);
l_Lean_IR_CtorFieldInfo_instToFormat = _init_l_Lean_IR_CtorFieldInfo_instToFormat();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormat);
l_Lean_IR_instInhabitedCtorLayout___closed__0 = _init_l_Lean_IR_instInhabitedCtorLayout___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorLayout___closed__0);
l_Lean_IR_instInhabitedCtorLayout___closed__1 = _init_l_Lean_IR_instInhabitedCtorLayout___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorLayout___closed__1);
l_Lean_IR_instInhabitedCtorLayout___closed__2 = _init_l_Lean_IR_instInhabitedCtorLayout___closed__2();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorLayout___closed__2);
l_Lean_IR_instInhabitedCtorLayout = _init_l_Lean_IR_instInhabitedCtorLayout();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorLayout);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR_ToIRType___hyg_999_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_ctorLayoutExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_ctorLayoutExt);
lean_dec_ref(res);
}l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0 = _init_l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_getCtorLayout_fillCache_spec__2___closed__0);
l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0 = _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__0);
l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1 = _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__1);
l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2 = _init_l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Lean_IR_getCtorLayout_fillCache_spec__3___closed__2);
l_Lean_IR_getCtorLayout_fillCache___closed__0 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__0();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__0);
l_Lean_IR_getCtorLayout_fillCache___closed__1 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__1();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__1);
l_Lean_IR_getCtorLayout_fillCache___closed__2 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__2();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__2);
l_Lean_IR_getCtorLayout_fillCache___closed__3 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__3();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__3);
l_Lean_IR_getCtorLayout_fillCache___closed__4 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__4();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__4);
l_Lean_IR_getCtorLayout_fillCache___closed__5 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__5();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__5);
l_Lean_IR_getCtorLayout_fillCache___closed__6 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__6();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__6);
l_Lean_IR_getCtorLayout_fillCache___closed__7 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__7();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__7);
l_Lean_IR_getCtorLayout_fillCache___closed__8 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__8();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__8);
l_Lean_IR_getCtorLayout_fillCache___closed__9 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__9();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__9);
l_Lean_IR_getCtorLayout_fillCache___closed__10 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__10();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__10);
l_Lean_IR_getCtorLayout_fillCache___closed__11 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__11();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__11);
l_Lean_IR_getCtorLayout_fillCache___closed__12 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__12();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__12);
l_Lean_IR_getCtorLayout_fillCache___closed__13 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__13();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__13);
l_Lean_IR_getCtorLayout_fillCache___closed__14 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__14();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__14);
l_Lean_IR_getCtorLayout_fillCache___closed__15 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__15();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__15);
l_Lean_IR_getCtorLayout_fillCache___closed__16 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__16();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__16);
l_Lean_IR_getCtorLayout_fillCache___closed__17 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__17();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__17);
l_Lean_IR_getCtorLayout_fillCache___closed__18 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__18();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__18);
l_Lean_IR_getCtorLayout_fillCache___closed__19 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__19();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__19);
l_Lean_IR_getCtorLayout_fillCache___closed__20 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__20();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__20);
l_Lean_IR_getCtorLayout_fillCache___closed__21 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__21();
l_Lean_IR_getCtorLayout_fillCache___closed__22 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__22();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__22);
l_Lean_IR_getCtorLayout_fillCache___closed__23 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__23();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__23);
l_Lean_IR_getCtorLayout_fillCache___closed__24 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__24();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__24);
l_Lean_IR_getCtorLayout_fillCache___closed__25 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__25();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__25);
l_Lean_IR_getCtorLayout_fillCache___closed__26 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__26();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__26);
l_Lean_IR_getCtorLayout_fillCache___closed__27 = _init_l_Lean_IR_getCtorLayout_fillCache___closed__27();
lean_mark_persistent(l_Lean_IR_getCtorLayout_fillCache___closed__27);
l_Lean_IR_getCtorLayout___closed__0 = _init_l_Lean_IR_getCtorLayout___closed__0();
lean_mark_persistent(l_Lean_IR_getCtorLayout___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
