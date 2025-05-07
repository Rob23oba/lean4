// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Simp.BuiltinSimprocs.List
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Grind", 5, 5);
x_5 = lean_mk_string_unchecked("normExt", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Lean_Meta_mkSimpExt(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_4);
x_12 = l_Lean_Meta_Grind_normExt;
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1000u);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_14);
x_19 = lean_unbox(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_addSimpTheorem(x_12, x_13, x_17, x_18, x_19, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_22;
x_9 = x_21;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_4);
x_12 = l_Lean_Meta_Grind_normExt;
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1000u);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_addSimpTheorem(x_12, x_13, x_10, x_17, x_18, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_4 = x_21;
x_9 = x_20;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Meta_Grind_normExt;
x_9 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_8, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_mk_string_unchecked("`grind` normalization theorems have already been initialized", 60, 60);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_box(0);
x_18 = lean_array_size(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_1, x_18, x_20, x_17, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_array_size(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_2, x_23, x_20, x_17, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_17);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
return x_24;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_registerNormTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_mk_string_unchecked("Bool", 4, 4);
x_17 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_16);
x_18 = l_Lean_Name_mkStr2(x_16, x_17);
x_19 = lean_name_eq(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_mk_string_unchecked("or", 2, 2);
x_21 = l_Lean_Name_mkStr2(x_16, x_20);
x_22 = lean_name_eq(x_1, x_21);
lean_dec(x_21);
x_2 = x_22;
goto block_15;
}
else
{
lean_dec(x_16);
x_2 = x_19;
goto block_15;
}
block_15:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_mk_string_unchecked("Bool", 4, 4);
x_4 = lean_mk_string_unchecked("not", 3, 3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_name_eq(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("BEq", 3, 3);
x_8 = lean_mk_string_unchecked("beq", 3, 3);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_name_eq(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_mk_string_unchecked("Decidable", 9, 9);
x_12 = lean_mk_string_unchecked("decide", 6, 6);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_name_eq(x_1, x_13);
lean_dec(x_13);
return x_14;
}
else
{
return x_10;
}
}
else
{
return x_6;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; uint8_t x_19; 
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_18 = l_Lean_Expr_cleanupAnnotations(x_11);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_17;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_18);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_20);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = lean_mk_string_unchecked("Eq", 2, 2);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_71; 
lean_dec(x_13);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_71 = l_Lean_Expr_getAppFn(x_28);
switch (lean_obj_tag(x_71)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Expr_bvar___override(x_72);
x_74 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_73);
return x_74;
}
case 1:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l_Lean_Expr_fvar___override(x_75);
x_77 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_76);
return x_77;
}
case 2:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = l_Lean_Expr_mvar___override(x_78);
x_80 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_79);
return x_80;
}
case 3:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = l_Lean_Expr_sort___override(x_81);
x_83 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_82);
return x_83;
}
case 4:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_102; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
lean_dec(x_71);
x_163 = lean_mk_string_unchecked("Bool", 4, 4);
x_164 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_163);
x_165 = l_Lean_Name_mkStr2(x_163, x_164);
x_166 = lean_name_eq(x_84, x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_mk_string_unchecked("false", 5, 5);
x_168 = l_Lean_Name_mkStr2(x_163, x_167);
x_169 = lean_name_eq(x_84, x_168);
lean_dec(x_168);
x_102 = x_169;
goto block_162;
}
else
{
lean_dec(x_163);
x_102 = x_166;
goto block_162;
}
block_101:
{
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_85);
lean_dec(x_85);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_84);
lean_dec(x_84);
x_31 = x_88;
goto block_70;
}
else
{
lean_dec(x_84);
x_31 = x_87;
goto block_70;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_inc(x_29);
lean_inc(x_28);
x_89 = l_Lean_mkApp3(x_24, x_30, x_28, x_29);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Grind", 5, 5);
x_92 = lean_mk_string_unchecked("flip_bool_eq", 12, 12);
x_93 = l_Lean_Name_mkStr3(x_90, x_91, x_92);
x_94 = lean_box(0);
x_95 = l_Lean_Expr_const___override(x_93, x_94);
x_96 = l_Lean_mkAppB(x_95, x_29, x_28);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_27);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_12);
return x_100;
}
}
block_162:
{
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Lean_Expr_getAppFn(x_29);
switch (lean_obj_tag(x_103)) {
case 0:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Expr_bvar___override(x_104);
x_106 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_105);
return x_106;
}
case 1:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec(x_103);
x_108 = l_Lean_Expr_fvar___override(x_107);
x_109 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_108);
return x_109;
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec(x_103);
x_111 = l_Lean_Expr_mvar___override(x_110);
x_112 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_111);
return x_112;
}
case 3:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
lean_dec(x_103);
x_114 = l_Lean_Expr_sort___override(x_113);
x_115 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_114);
return x_115;
}
case 4:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_103, 0);
lean_inc(x_116);
lean_dec(x_103);
x_117 = lean_mk_string_unchecked("Bool", 4, 4);
x_118 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_117);
x_119 = l_Lean_Name_mkStr2(x_117, x_118);
x_120 = lean_name_eq(x_116, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_mk_string_unchecked("false", 5, 5);
x_122 = l_Lean_Name_mkStr2(x_117, x_121);
x_123 = lean_name_eq(x_116, x_122);
lean_dec(x_122);
x_85 = x_116;
x_86 = x_123;
goto block_101;
}
else
{
lean_dec(x_117);
x_85 = x_116;
x_86 = x_120;
goto block_101;
}
}
case 5:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_dec(x_103);
x_126 = l_Lean_Expr_app___override(x_124, x_125);
x_127 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_126);
return x_127;
}
case 6:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_128 = lean_ctor_get(x_103, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_103, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_103, 2);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_103, sizeof(void*)*3 + 8);
lean_dec(x_103);
x_132 = l_Lean_Expr_lam___override(x_128, x_129, x_130, x_131);
x_133 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_132);
return x_133;
}
case 7:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_134 = lean_ctor_get(x_103, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_103, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_103, 2);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_103, sizeof(void*)*3 + 8);
lean_dec(x_103);
x_138 = l_Lean_Expr_forallE___override(x_134, x_135, x_136, x_137);
x_139 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_138);
return x_139;
}
case 8:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_140 = lean_ctor_get(x_103, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_103, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_103, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_103, 3);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_103, sizeof(void*)*4 + 8);
lean_dec(x_103);
x_145 = l_Lean_Expr_letE___override(x_140, x_141, x_142, x_143, x_144);
x_146 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_145);
return x_146;
}
case 9:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_147 = lean_ctor_get(x_103, 0);
lean_inc(x_147);
lean_dec(x_103);
x_148 = l_Lean_Expr_lit___override(x_147);
x_149 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_148);
return x_149;
}
case 10:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_150 = lean_ctor_get(x_103, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_103, 1);
lean_inc(x_151);
lean_dec(x_103);
x_152 = l_Lean_Expr_mdata___override(x_150, x_151);
x_153 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_152);
return x_153;
}
default: 
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_154 = lean_ctor_get(x_103, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_103, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_103, 2);
lean_inc(x_156);
lean_dec(x_103);
x_157 = l_Lean_Expr_proj___override(x_154, x_155, x_156);
x_158 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_12);
return x_161;
}
}
}
case 5:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_170 = lean_ctor_get(x_71, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_71, 1);
lean_inc(x_171);
lean_dec(x_71);
x_172 = l_Lean_Expr_app___override(x_170, x_171);
x_173 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_172, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_172);
return x_173;
}
case 6:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_174 = lean_ctor_get(x_71, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_71, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_71, 2);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 8);
lean_dec(x_71);
x_178 = l_Lean_Expr_lam___override(x_174, x_175, x_176, x_177);
x_179 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_178, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_178);
return x_179;
}
case 7:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_180 = lean_ctor_get(x_71, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_71, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_71, 2);
lean_inc(x_182);
x_183 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 8);
lean_dec(x_71);
x_184 = l_Lean_Expr_forallE___override(x_180, x_181, x_182, x_183);
x_185 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_184);
return x_185;
}
case 8:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_186 = lean_ctor_get(x_71, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_71, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_71, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_71, 3);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_71, sizeof(void*)*4 + 8);
lean_dec(x_71);
x_191 = l_Lean_Expr_letE___override(x_186, x_187, x_188, x_189, x_190);
x_192 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_191, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_191);
return x_192;
}
case 9:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_193 = lean_ctor_get(x_71, 0);
lean_inc(x_193);
lean_dec(x_71);
x_194 = l_Lean_Expr_lit___override(x_193);
x_195 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_194);
return x_195;
}
case 10:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_196 = lean_ctor_get(x_71, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_71, 1);
lean_inc(x_197);
lean_dec(x_71);
x_198 = l_Lean_Expr_mdata___override(x_196, x_197);
x_199 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_198, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_198);
return x_199;
}
default: 
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
x_200 = lean_ctor_get(x_71, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_71, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_71, 2);
lean_inc(x_202);
lean_dec(x_71);
x_203 = l_Lean_Expr_proj___override(x_200, x_201, x_202);
x_204 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_203, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_203);
return x_204;
}
}
block_70:
{
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_12);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_mk_string_unchecked("Bool", 4, 4);
x_36 = lean_mk_string_unchecked("true", 4, 4);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Expr_const___override(x_37, x_38);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_30);
lean_inc(x_24);
x_40 = l_Lean_mkApp3(x_24, x_30, x_29, x_39);
lean_inc(x_28);
x_41 = l_Lean_mkApp3(x_24, x_30, x_28, x_39);
x_42 = l_Lean_Meta_mkEq(x_40, x_41, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_mk_string_unchecked("Lean", 4, 4);
x_46 = lean_mk_string_unchecked("Grind", 5, 5);
x_47 = lean_mk_string_unchecked("bool_eq_to_prop", 15, 15);
x_48 = l_Lean_Name_mkStr3(x_45, x_46, x_47);
x_49 = l_Lean_Expr_const___override(x_48, x_38);
x_50 = l_Lean_mkAppB(x_49, x_29, x_28);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_27);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("Grind", 5, 5);
x_58 = lean_mk_string_unchecked("bool_eq_to_prop", 15, 15);
x_59 = l_Lean_Name_mkStr3(x_56, x_57, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_38);
x_61 = l_Lean_mkAppB(x_60, x_29, x_28);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_27);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_29);
lean_dec(x_28);
x_66 = !lean_is_exclusive(x_42);
if (x_66 == 0)
{
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpBoolEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpBoolEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Grind", 5, 5);
x_5 = lean_mk_string_unchecked("simpBoolEq", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("Bool", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(3);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_10);
x_19 = lean_array_push(x_18, x_14);
x_20 = lean_array_push(x_19, x_15);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpBoolEq___boxed), 9, 0);
x_23 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_6, x_21, x_22, x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("List", 4, 4);
x_8 = lean_mk_string_unchecked("reduceReplicate", 15, 15);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = l_Lean_Meta_Simp_Simprocs_erase(x_5, x_9);
x_11 = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(x_10, x_1, x_2, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_addPreMatchCondSimproc(x_12, x_1, x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Meta", 4, 4);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = lean_mk_string_unchecked("simpBoolEq", 10, 10);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Meta_Simp_Simprocs_add(x_15, x_21, x_23, x_1, x_2, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_array_push(x_28, x_26);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_array_push(x_33, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getSimprocs___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = l_Lean_Meta_Grind_normExt;
x_8 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getSimpCongrTheorems(x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(100000u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_box(0);
x_17 = lean_box(1);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 15);
x_19 = lean_box(0);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 14);
x_21 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_22);
x_23 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 1, x_23);
x_24 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 2, x_24);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 3, x_18);
x_25 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 4, x_25);
x_26 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 5, x_26);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 6, x_27);
x_28 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 7, x_28);
x_29 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 8, x_29);
x_30 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 9, x_30);
x_31 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 10, x_31);
x_32 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 11, x_32);
x_33 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 12, x_33);
x_34 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 13, x_34);
x_35 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 14, x_35);
x_36 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 15, x_36);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 16, x_20);
x_37 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 17, x_37);
x_38 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 18, x_38);
x_39 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 19, x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_array_push(x_41, x_9);
x_43 = l_Lean_Meta_Simp_mkContext(x_21, x_42, x_12, x_2, x_3, x_4, x_5, x_13);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Grind_getSimpContext(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Meta_Grind_getSimprocs___redArg(x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_ctor_set(x_8, 1, x_18);
lean_ctor_set(x_8, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_to_nat(x_22);
x_24 = lean_nat_pow(x_20, x_23);
lean_dec(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = lean_usize_to_nat(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_18);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set_usize(x_29, 4, x_22);
lean_inc(x_17);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_simp(x_1, x_10, x_13, x_15, x_31, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = l_Lean_Meta_Grind_getSimprocs___redArg(x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_unsigned_to_nat(0u);
lean_inc(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_56);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_unsigned_to_nat(5u);
x_63 = lean_usize_of_nat(x_62);
x_64 = lean_usize_to_nat(x_63);
x_65 = lean_nat_pow(x_61, x_64);
lean_dec(x_64);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = lean_usize_to_nat(x_66);
x_68 = lean_mk_empty_array_with_capacity(x_67);
lean_dec(x_67);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_58);
lean_ctor_set(x_70, 3, x_58);
lean_ctor_set_usize(x_70, 4, x_63);
lean_inc(x_57);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_57);
lean_ctor_set(x_71, 2, x_60);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_simp(x_1, x_50, x_53, x_55, x_72, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_ctor_get(x_52, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_52, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_86 = x_52;
} else {
 lean_dec_ref(x_52);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
