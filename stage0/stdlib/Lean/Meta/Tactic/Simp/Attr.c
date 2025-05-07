// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Attr
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_926_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_900_(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_logWarning___at___Lean_Linter_initFn____x40_Lean_Linter_Deprecated___hyg_88__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sevalSimpExtension;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_831_;
lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_Environment_findAsync_x3f(x_12, x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_8);
x_14 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("'", 1, 1);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_22, x_3, x_4, x_5, x_6, x_11);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l_Lean_Environment_findAsync_x3f(x_27, x_1, x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Expr_const___override(x_1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("'", 1, 1);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_37, x_3, x_4, x_5, x_6, x_26);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_17 = lean_array_uget(x_6, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_addSimpTheorem(x_1, x_17, x_2, x_3, x_4, x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_8, x_22);
x_8 = x_23;
x_9 = x_20;
x_14 = x_19;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_21; 
x_7 = lean_mk_string_unchecked("'", 1, 1);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_9 = x_21;
goto block_20;
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = l_Lean_MessageData_ofName(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_logWarning___at___Lean_Linter_initFn____x40_Lean_Linter_Deprecated___hyg_88__spec__0(x_14, x_4, x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_19; 
lean_inc(x_1);
x_19 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_19 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_inc(x_1);
x_21 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_1, 5);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_22, x_20);
lean_dec(x_20);
x_6 = x_23;
goto block_18;
}
else
{
lean_dec(x_20);
x_6 = x_21;
goto block_18;
}
}
else
{
x_6 = x_19;
goto block_18;
}
}
else
{
x_6 = x_19;
goto block_18;
}
block_18:
{
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_Meta_Origin_converse(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0(x_1, x_2, x_8, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0(x_1, x_2, x_12, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_1);
x_15 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_1, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_19 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_22, x_3, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_11);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_array_size(x_26);
x_28 = lean_usize_of_nat(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_2);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1(x_2, x_5, x_6, x_3, x_7, x_26, x_27, x_28, x_8, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_inc(x_1);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 0, x_1);
lean_inc(x_12);
lean_inc(x_2);
x_33 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_29, x_3, x_10, x_11, x_12, x_13, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_1, x_13, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_free_object(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_8);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
lean_ctor_set(x_20, 0, x_1);
x_43 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_20, x_3, x_10, x_11, x_12, x_13, x_42);
lean_dec(x_13);
lean_dec(x_11);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
lean_inc(x_1);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_26);
lean_inc(x_12);
lean_inc(x_2);
x_46 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_45, x_3, x_10, x_11, x_12, x_13, x_44);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_1);
x_48 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_1, x_13, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_8);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
lean_ctor_set(x_20, 0, x_1);
x_55 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_20, x_3, x_10, x_11, x_12, x_13, x_54);
lean_dec(x_13);
lean_dec(x_11);
return x_55;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_20, 0);
lean_inc(x_56);
lean_dec(x_20);
x_57 = lean_array_size(x_56);
x_58 = lean_usize_of_nat(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_2);
x_59 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1(x_2, x_5, x_6, x_3, x_7, x_56, x_57, x_58, x_8, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(2, 2, 0);
} else {
 x_62 = x_61;
 lean_ctor_set_tag(x_62, 2);
}
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_56);
lean_inc(x_12);
lean_inc(x_2);
x_63 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_62, x_3, x_10, x_11, x_12, x_13, x_60);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_1);
x_65 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_1, x_13, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_8);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_8);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_72, x_3, x_10, x_11, x_12, x_13, x_71);
lean_dec(x_13);
lean_dec(x_11);
return x_73;
}
}
else
{
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_59;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_19);
if (x_74 == 0)
{
return x_19;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_19, 0);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_19);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_8);
lean_dec(x_7);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_1);
x_80 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_2, x_79, x_3, x_10, x_11, x_12, x_13, x_78);
lean_dec(x_13);
lean_dec(x_11);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_81; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_3);
x_182 = l_Lean_Meta_Simp_isSimproc___redArg(x_3, x_7, x_8);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_6, x_7, x_185);
x_81 = x_186;
goto block_181;
}
else
{
x_81 = x_182;
goto block_181;
}
block_18:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
block_66:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_4, x_28);
lean_dec(x_4);
x_30 = l_Lean_getAttrParamOptPrio(x_29, x_6, x_7, x_22);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
x_34 = lean_task_get_own(x_33);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_25);
lean_inc(x_20);
x_36 = l_Lean_Meta_isProp(x_35, x_20, x_25, x_6, x_7, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; 
x_39 = lean_ctor_get_uint8(x_26, sizeof(void*)*3);
lean_dec(x_26);
x_40 = lean_box(x_39);
if (lean_obj_tag(x_40) == 0)
{
if (x_27 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
lean_inc(x_25);
lean_inc(x_23);
x_42 = l_Lean_Meta_mkSimpAttr___lam__0(x_3, x_1, x_5, x_21, x_19, x_24, x_31, x_23, x_23, x_20, x_25, x_6, x_7, x_41);
lean_dec(x_20);
x_9 = x_25;
x_10 = x_23;
x_11 = x_42;
goto block_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_1);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_mk_string_unchecked("invalid '←' modifier, '", 25, 23);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_3);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("' is a declaration name to be unfolded", 38, 38);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_50, x_20, x_25, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_20);
x_9 = x_25;
x_10 = x_23;
x_11 = x_51;
goto block_18;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_mk_string_unchecked("invalid 'simp', it is not a proposition nor a definition (to unfold)", 68, 68);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_54, x_20, x_25, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_20);
x_9 = x_25;
x_10 = x_23;
x_11 = x_55;
goto block_18;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_26);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_dec(x_36);
lean_inc(x_25);
x_57 = l_Lean_Meta_addSimpTheorem(x_1, x_3, x_19, x_27, x_5, x_31, x_20, x_25, x_6, x_7, x_56);
lean_dec(x_20);
x_9 = x_25;
x_10 = x_23;
x_11 = x_57;
goto block_18;
}
}
else
{
uint8_t x_58; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
return x_36;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_30);
if (x_62 == 0)
{
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_30, 0);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_80:
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Syntax_getArg(x_4, x_76);
x_79 = l_Lean_Syntax_isNone(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
x_19 = x_77;
x_20 = x_75;
x_21 = x_67;
x_22 = x_68;
x_23 = x_69;
x_24 = x_70;
x_25 = x_74;
x_26 = x_71;
x_27 = x_72;
goto block_66;
}
else
{
x_19 = x_77;
x_20 = x_75;
x_21 = x_67;
x_22 = x_68;
x_23 = x_69;
x_24 = x_70;
x_25 = x_74;
x_26 = x_71;
x_27 = x_73;
goto block_66;
}
}
block_181:
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; lean_object* x_90; lean_object* x_91; size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint64_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; lean_object* x_152; 
lean_dec(x_2);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_box(0);
x_86 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_unsigned_to_nat(5u);
x_89 = lean_usize_of_nat(x_88);
x_90 = lean_usize_to_nat(x_89);
x_91 = lean_nat_pow(x_87, x_90);
lean_dec(x_90);
x_92 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_93 = lean_usize_to_nat(x_92);
x_94 = lean_mk_empty_array_with_capacity(x_93);
lean_dec(x_93);
lean_inc(x_94);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_unsigned_to_nat(0u);
lean_inc(x_86);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_86);
lean_inc(x_86);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_86);
lean_inc(x_86);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_86);
lean_inc(x_86);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_86);
lean_inc(x_86);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_86);
lean_inc(x_86);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_86);
lean_inc(x_97);
x_103 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_96);
lean_ctor_set(x_103, 2, x_96);
lean_ctor_set(x_103, 3, x_97);
lean_ctor_set(x_103, 4, x_98);
lean_ctor_set(x_103, 5, x_99);
lean_ctor_set(x_103, 6, x_100);
lean_ctor_set(x_103, 7, x_101);
lean_ctor_set(x_103, 8, x_102);
lean_inc(x_86);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_86);
lean_inc(x_86);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_86);
lean_inc(x_86);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_86);
lean_inc(x_86);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_86);
lean_inc(x_107);
lean_inc(x_104);
x_108 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_107);
lean_inc(x_94);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_94);
lean_inc(x_94);
x_110 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_94);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_96);
lean_ctor_set_usize(x_110, 4, x_89);
lean_inc(x_86);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_86);
lean_inc_n(x_97, 2);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_97);
lean_ctor_set(x_112, 2, x_97);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_108);
lean_ctor_set(x_113, 2, x_85);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_112);
x_114 = lean_st_mk_ref(x_113, x_84);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_box(1);
x_118 = lean_box(0);
x_119 = lean_box(2);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_86);
x_121 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_121, 0, x_95);
lean_ctor_set(x_121, 1, x_94);
lean_ctor_set(x_121, 2, x_96);
lean_ctor_set(x_121, 3, x_96);
lean_ctor_set_usize(x_121, 4, x_89);
x_122 = lean_box(1);
x_123 = lean_alloc_ctor(0, 0, 18);
x_124 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 0, x_124);
x_125 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 1, x_125);
x_126 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 2, x_126);
x_127 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 3, x_127);
x_128 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 4, x_128);
x_129 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 5, x_129);
x_130 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 6, x_130);
x_131 = lean_unbox(x_82);
lean_ctor_set_uint8(x_123, 7, x_131);
x_132 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 8, x_132);
x_133 = lean_unbox(x_117);
lean_ctor_set_uint8(x_123, 9, x_133);
x_134 = lean_unbox(x_118);
lean_ctor_set_uint8(x_123, 10, x_134);
x_135 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 11, x_135);
x_136 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 12, x_136);
x_137 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 13, x_137);
x_138 = lean_unbox(x_119);
lean_ctor_set_uint8(x_123, 14, x_138);
x_139 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 15, x_139);
x_140 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 16, x_140);
x_141 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, 17, x_141);
x_142 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_123);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_120);
lean_ctor_set(x_143, 1, x_121);
lean_ctor_set(x_143, 2, x_85);
x_144 = lean_mk_empty_array_with_capacity(x_96);
x_145 = lean_box(0);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_147, 0, x_123);
lean_ctor_set(x_147, 1, x_85);
lean_ctor_set(x_147, 2, x_143);
lean_ctor_set(x_147, 3, x_144);
lean_ctor_set(x_147, 4, x_145);
lean_ctor_set(x_147, 5, x_96);
lean_ctor_set(x_147, 6, x_146);
lean_ctor_set_uint64(x_147, sizeof(void*)*7, x_142);
x_148 = lean_unbox(x_82);
lean_ctor_set_uint8(x_147, sizeof(void*)*7 + 8, x_148);
x_149 = lean_unbox(x_82);
lean_ctor_set_uint8(x_147, sizeof(void*)*7 + 9, x_149);
x_150 = lean_unbox(x_82);
lean_ctor_set_uint8(x_147, sizeof(void*)*7 + 10, x_150);
x_151 = lean_unbox(x_82);
lean_inc(x_3);
x_152 = l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0(x_3, x_151, x_147, x_115, x_6, x_7, x_116);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_box(0);
x_156 = lean_unsigned_to_nat(1u);
x_157 = l_Lean_Syntax_getArg(x_4, x_156);
x_158 = l_Lean_Syntax_isNone(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; 
x_159 = l_Lean_Syntax_getArg(x_157, x_96);
lean_dec(x_157);
x_160 = l_Lean_Syntax_getKind(x_159);
x_161 = lean_mk_string_unchecked("Lean", 4, 4);
x_162 = lean_mk_string_unchecked("Parser", 6, 6);
x_163 = lean_mk_string_unchecked("Tactic", 6, 6);
x_164 = lean_mk_string_unchecked("simpPost", 8, 8);
x_165 = l_Lean_Name_mkStr4(x_161, x_162, x_163, x_164);
x_166 = lean_name_eq(x_160, x_165);
lean_dec(x_165);
lean_dec(x_160);
x_167 = lean_unbox(x_82);
x_168 = lean_unbox(x_122);
x_169 = lean_unbox(x_82);
lean_dec(x_82);
x_67 = x_96;
x_68 = x_154;
x_69 = x_155;
x_70 = x_167;
x_71 = x_153;
x_72 = x_168;
x_73 = x_169;
x_74 = x_115;
x_75 = x_147;
x_76 = x_87;
x_77 = x_166;
goto block_80;
}
else
{
uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; 
lean_dec(x_157);
x_170 = lean_unbox(x_82);
x_171 = lean_unbox(x_122);
x_172 = lean_unbox(x_82);
lean_dec(x_82);
x_173 = lean_unbox(x_122);
x_67 = x_96;
x_68 = x_154;
x_69 = x_155;
x_70 = x_170;
x_71 = x_153;
x_72 = x_171;
x_73 = x_172;
x_74 = x_115;
x_75 = x_147;
x_76 = x_87;
x_77 = x_173;
goto block_80;
}
}
else
{
uint8_t x_174; 
lean_dec(x_147);
lean_dec(x_115);
lean_dec(x_82);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_152);
if (x_174 == 0)
{
return x_152;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_152, 0);
x_176 = lean_ctor_get(x_152, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_152);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_82);
lean_dec(x_1);
x_178 = lean_ctor_get(x_81, 1);
lean_inc(x_178);
lean_dec(x_81);
x_179 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_180 = l_Lean_Attribute_add(x_3, x_179, x_4, x_5, x_6, x_7, x_178);
return x_180;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_inc(x_3);
x_74 = l_Lean_Meta_Simp_isSimproc___redArg(x_3, x_5, x_6);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_4, x_5, x_77);
x_7 = x_78;
goto block_73;
}
else
{
x_7 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_instInhabitedSimpTheorems;
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_20 = l_Lean_ScopedEnvExtension_getState___redArg(x_16, x_1, x_15, x_19);
x_21 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_21, 0, x_3);
x_22 = lean_unbox(x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_unbox(x_8);
lean_dec(x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_23);
x_24 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2(x_20, x_21, x_4, x_5, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_5, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 2, 1);
lean_closure_set(x_31, 0, x_25);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_1, x_32, x_31);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_38);
lean_ctor_set(x_27, 1, x_38);
lean_ctor_set(x_27, 0, x_38);
x_39 = lean_ctor_get(x_29, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 7);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_27);
lean_ctor_set(x_42, 5, x_39);
lean_ctor_set(x_42, 6, x_40);
lean_ctor_set(x_42, 7, x_41);
x_43 = lean_st_ref_set(x_5, x_42, x_30);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__2___boxed), 2, 1);
lean_closure_set(x_52, 0, x_25);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_1, x_53, x_52);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 3);
lean_inc(x_57);
x_58 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_ctor_get(x_50, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_50, 7);
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_60);
lean_ctor_set(x_64, 5, x_61);
lean_ctor_set(x_64, 6, x_62);
lean_ctor_set(x_64, 7, x_63);
x_65 = lean_st_ref_set(x_5, x_64, x_51);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_8);
lean_dec(x_1);
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
lean_dec(x_7);
x_71 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_72 = l_Lean_Attribute_erase(x_3, x_71, x_4, x_5, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__1___boxed), 8, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lam__3), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
x_12 = l_Lean_registerBuiltinAttribute(x_11, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_getAsyncConstInfo___at___Lean_Meta_mkSimpAttr_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkSimpAttr_spec__1(x_1, x_15, x_16, x_17, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Meta_mkSimpAttr_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_mkSimpAttr___lam__0(x_1, x_2, x_15, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Meta_mkSimpAttr___lam__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_mkSimpAttr___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_831_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_mkSimpExt(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkSimpAttr(x_1, x_2, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_21; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_simpExtensionMapRef;
x_11 = lean_st_ref_take(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash___override(x_1);
x_26 = lean_unsigned_to_nat(32u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_unsigned_to_nat(16u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_sub(x_35, x_37);
x_39 = lean_usize_land(x_34, x_38);
x_40 = lean_array_uget(x_23, x_39);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_nat_add(x_22, x_36);
lean_dec(x_22);
lean_inc(x_6);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_6);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_array_uset(x_23, x_39, x_43);
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_nat_shiftl(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_44);
lean_ctor_set(x_12, 1, x_51);
lean_ctor_set(x_12, 0, x_42);
x_14 = x_12;
goto block_20;
}
else
{
lean_ctor_set(x_12, 1, x_44);
lean_ctor_set(x_12, 0, x_42);
x_14 = x_12;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_23, x_39, x_52);
lean_inc(x_6);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_6, x_40);
x_55 = lean_array_uset(x_53, x_39, x_54);
lean_ctor_set(x_12, 1, x_55);
x_14 = x_12;
goto block_20;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; lean_object* x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_array_get_size(x_57);
x_59 = l_Lean_Name_hash___override(x_1);
x_60 = lean_unsigned_to_nat(32u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_xor(x_59, x_62);
x_64 = lean_unsigned_to_nat(16u);
x_65 = lean_uint64_of_nat(x_64);
x_66 = lean_uint64_shift_right(x_63, x_65);
x_67 = lean_uint64_xor(x_63, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_usize_of_nat(x_70);
x_72 = lean_usize_sub(x_69, x_71);
x_73 = lean_usize_land(x_68, x_72);
x_74 = lean_array_uget(x_57, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_nat_add(x_56, x_70);
lean_dec(x_56);
lean_inc(x_6);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_6);
lean_ctor_set(x_77, 2, x_74);
x_78 = lean_array_uset(x_57, x_73, x_77);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_14 = x_86;
goto block_20;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_78);
x_14 = x_87;
goto block_20;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_box(0);
x_89 = lean_array_uset(x_57, x_73, x_88);
lean_inc(x_6);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_6, x_74);
x_91 = lean_array_uset(x_89, x_73, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_56);
lean_ctor_set(x_92, 1, x_91);
x_14 = x_92;
goto block_20;
}
}
block_20:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_set(x_10, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_6);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
return x_8;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_8, 0);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_8);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_900_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("simp", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("simplification theorem", 22, 22);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Meta", 4, 4);
x_7 = lean_mk_string_unchecked("simpExtension", 13, 13);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = l_Lean_Meta_registerSimpAttr(x_3, x_4, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_926_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("seval", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("symbolic evaluator theorem", 26, 26);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Meta", 4, 4);
x_7 = lean_mk_string_unchecked("sevalSimpExtension", 18, 18);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = l_Lean_Meta_registerSimpAttr(x_3, x_4, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_simpExtension;
x_4 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpTheorems___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSimpTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_sevalSimpExtension;
x_4 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSEvalTheorems___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSEvalTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSEvalTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_6 = l_Lean_Meta_getSimpTheorems___redArg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_getSimpCongrTheorems(x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(100000u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 1, x_19);
x_20 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 2, x_20);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 3, x_21);
x_22 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 4, x_22);
x_23 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 5, x_23);
x_24 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 6, x_24);
x_25 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 7, x_25);
x_26 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 8, x_26);
x_27 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 9, x_27);
x_28 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 10, x_28);
x_29 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 11, x_29);
x_30 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 12, x_30);
x_31 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 13, x_31);
x_32 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 14, x_32);
x_33 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 15, x_33);
x_34 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 16, x_34);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 17, x_35);
x_36 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 18, x_36);
x_37 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 19, x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_empty_array_with_capacity(x_38);
x_40 = lean_array_push(x_39, x_7);
x_41 = l_Lean_Meta_Simp_mkContext(x_17, x_40, x_10, x_1, x_2, x_3, x_4, x_11);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_Context_mkDefault(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_831_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_831_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_831_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_900_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_926_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_sevalSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_sevalSimpExtension);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
