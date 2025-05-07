// Lean compiler output
// Module: Lean.Meta.PPGoal
// Imports: Lean.Meta.InferType
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
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_auxDecls;
LEAN_EXPORT uint8_t l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_ppVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_showLetValues;
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_pushPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_implementationDetailHyps;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_45_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_85_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_pushPending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_pp_inaccessibleNames;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_5_(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_ppVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_125_(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("auxDecls", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("display auxiliary declarations used to compile recursive functions", 66, 66);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_45_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("implementationDetailHyps", 24, 24);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("display implementation detail hypotheses in the local context", 61, 61);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("inaccessibleNames", 17, 17);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("display inaccessible declarations in the local context", 54, 54);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_125_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("showLetValues", 13, 13);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("display let-declaration values in the info view", 47, 47);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Std_Format_isNil(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("\n", 1, 1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_isLHSGoal_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_mk_string_unchecked("⊢ ", 4, 2);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("| ", 2, 2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGoalPrefix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getGoalPrefix(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_alloc_closure((void*)(l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0___boxed), 1, 0);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_5, x_9, x_7);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_closure((void*)(l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0___boxed), 1, 0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_14, x_19, x_16);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed), 1, 0);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_5, x_8, x_6);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed), 1, 0);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Name_toString(x_11, x_14, x_12);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0(x_2, x_16, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_pushPending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___redArg(x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l_Lean_Meta_ppExpr(x_14, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_List_reverse___redArg(x_2);
x_19 = lean_mk_string_unchecked(" ", 1, 1);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_19);
x_20 = l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0(x_18, x_3);
x_21 = lean_mk_string_unchecked(" :", 2, 2);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = l_List_reverse___redArg(x_2);
x_35 = lean_mk_string_unchecked(" ", 1, 1);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_35);
x_36 = l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0(x_34, x_3);
x_37 = lean_mk_string_unchecked(" :", 2, 2);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
lean_dec(x_3);
x_50 = l_Lean_Meta_ppExpr(x_49, x_5, x_6, x_7, x_8, x_9);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l_List_reverse___redArg(x_2);
x_55 = lean_mk_string_unchecked(" ", 1, 1);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0(x_54, x_56);
x_58 = lean_mk_string_unchecked(" :", 2, 2);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_51);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_67);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_11);
lean_ctor_set(x_68, 1, x_66);
if (lean_is_scalar(x_53)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_53;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_52);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_9);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_foldl___at___Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_pushPending___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppGoal_pushPending(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_expr_eqv(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_ppVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_42; uint8_t x_43; 
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_13, x_8, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_simp_macro_scopes(x_12);
x_42 = lean_box(0);
x_43 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0(x_4, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_inc(x_15);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_15);
x_45 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0(x_4, x_44);
lean_dec(x_44);
x_19 = x_45;
goto block_41;
}
else
{
x_19 = x_43;
goto block_41;
}
block_41:
{
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
x_20 = l_Lean_Meta_ppGoal_pushPending(x_1, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
lean_dec(x_1);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_15);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
if (lean_is_scalar(x_17)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_17;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_16);
return x_40;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_46 = lean_ctor_get(x_6, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_6, 4);
lean_inc(x_48);
lean_dec(x_6);
lean_inc(x_1);
x_49 = l_Lean_Meta_ppGoal_pushPending(x_1, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_47, x_8, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Meta_ppExpr(x_54, x_7, x_8, x_9, x_10, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed), 1, 0);
x_62 = lean_simp_macro_scopes(x_46);
x_63 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_50);
x_76 = lean_box(1);
x_77 = lean_unbox(x_76);
x_78 = l_Lean_Name_toString(x_62, x_77, x_61);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_mk_string_unchecked(" : ", 3, 3);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_58);
if (x_2 == 0)
{
lean_dec(x_48);
lean_dec(x_1);
x_64 = x_83;
x_65 = x_59;
goto block_75;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_48, x_8, x_59);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = l_Lean_Meta_ppExpr(x_86, x_7, x_8, x_9, x_10, x_87);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = lean_mk_string_unchecked(" :=", 3, 3);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_tag(x_88, 5);
lean_ctor_set(x_88, 1, x_93);
lean_ctor_set(x_88, 0, x_83);
x_94 = lean_box(1);
lean_ctor_set_tag(x_84, 5);
lean_ctor_set(x_84, 1, x_90);
lean_ctor_set(x_84, 0, x_94);
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_84);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
x_64 = x_96;
x_65 = x_91;
goto block_75;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_mk_string_unchecked(" :=", 3, 3);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_83);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_box(1);
lean_ctor_set_tag(x_84, 5);
lean_ctor_set(x_84, 1, x_97);
lean_ctor_set(x_84, 0, x_102);
x_103 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_84);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_64 = x_104;
x_65 = x_98;
goto block_75;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_84, 0);
x_106 = lean_ctor_get(x_84, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_84);
x_107 = l_Lean_Meta_ppExpr(x_105, x_7, x_8, x_9, x_10, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_mk_string_unchecked(" :=", 3, 3);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(5, 2, 0);
} else {
 x_113 = x_110;
 lean_ctor_set_tag(x_113, 5);
}
lean_ctor_set(x_113, 0, x_83);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_box(1);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_108);
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_64 = x_117;
x_65 = x_109;
goto block_75;
}
}
block_75:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_67, 0, x_64);
x_68 = lean_unbox(x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_56)) {
 x_69 = lean_alloc_ctor(5, 2, 0);
} else {
 x_69 = x_56;
 lean_ctor_set_tag(x_69, 5);
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box(0);
x_71 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_52;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_60)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_60;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Meta_ppGoal_ppVars_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal_ppVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_ppGoal_ppVars(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_18; uint8_t x_22; 
x_22 = lean_usize_dec_eq(x_3, x_4);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
x_11 = x_5;
x_12 = x_10;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_1, 2);
x_30 = l_Lean_Meta_pp_implementationDetailHyps;
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Meta_pp_showLetValues;
x_33 = l_Lean_Meta_pp_auxDecls;
x_34 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_29, x_30);
x_35 = lean_nat_to_int(x_31);
x_36 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_29, x_32);
x_41 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_29, x_33);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_42 == 0)
{
goto block_40;
}
else
{
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_11 = x_5;
x_12 = x_10;
goto block_17;
}
}
else
{
goto block_40;
}
block_40:
{
if (x_34 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_LocalDecl_isImplementationDetail(x_25);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_5);
x_38 = l_Lean_Meta_ppGoal_ppVars(x_35, x_36, x_26, x_27, x_28, x_25, x_6, x_7, x_8, x_9, x_10);
x_18 = x_38;
goto block_21;
}
else
{
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_11 = x_5;
x_12 = x_10;
goto block_17;
}
}
else
{
lean_object* x_39; 
lean_dec(x_5);
x_39 = l_Lean_Meta_ppGoal_ppVars(x_35, x_36, x_26, x_27, x_28, x_25, x_6, x_7, x_8, x_9, x_10);
x_18 = x_39;
goto block_21;
}
}
}
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_11 = x_19;
x_12 = x_20;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_10);
x_17 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_9, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_20);
x_27 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_28 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_19, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_13 = lean_usize_shift_right(x_3, x_4);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_12, x_11, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_shift_left(x_17, x_4);
x_19 = lean_usize_sub(x_18, x_17);
x_20 = lean_usize_land(x_3, x_19);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_4, x_22);
x_24 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0(x_1, x_15, x_20, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_nat_add(x_14, x_16);
lean_dec(x_14);
x_28 = lean_array_get_size(x_11);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
return x_24;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
return x_24;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
lean_dec(x_24);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_11, x_31, x_32, x_25, x_6, x_7, x_8, x_9, x_26);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_usize_to_nat(x_3);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_42 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_43 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_34, x_41, x_42, x_5, x_6, x_7, x_8, x_9, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_nat_dec_le(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_ctor_get_usize(x_2, 4);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0(x_1, x_14, x_15, x_16, x_3, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_10, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
return x_17;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
return x_17;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
lean_dec(x_17);
x_24 = lean_usize_of_nat(x_10);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_20, x_24, x_25, x_18, x_5, x_6, x_7, x_8, x_19);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_nat_sub(x_4, x_12);
x_29 = lean_array_get_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_36 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_27, x_34, x_35, x_3, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0(x_1, x_37, x_3, x_5, x_6, x_7, x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_lt(x_10, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
return x_38;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
return x_38;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_38);
x_45 = lean_usize_of_nat(x_10);
x_46 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_47 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_41, x_45, x_46, x_39, x_5, x_6, x_7, x_8, x_40);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_mk_string_unchecked("case ", 5, 5);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_erase_macro_scopes(x_3);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Name_toString(x_11, x_13, x_1);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("\n", 1, 1);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_5);
x_21 = l_Lean_Meta_ppGoal_pushPending(x_5, x_17, x_19, x_20, x_8, x_9, x_10, x_11, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
x_26 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_25, x_9, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Meta_ppExpr(x_28, x_8, x_9, x_10, x_11, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_23);
x_35 = l_Lean_Meta_getGoalPrefix(x_6);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_34);
lean_ctor_set_tag(x_21, 4);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set_tag(x_15, 5);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_26);
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
lean_dec(x_6);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_dec(x_7);
lean_ctor_set(x_30, 0, x_15);
return x_30;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_30);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Name_str___override(x_38, x_39);
x_41 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_40, x_8, x_9, x_10, x_11, x_33);
return x_41;
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_30);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l_Lean_Name_num___override(x_42, x_43);
x_45 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_44, x_8, x_9, x_10, x_11, x_33);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_23);
x_49 = l_Lean_Meta_getGoalPrefix(x_6);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 1, x_50);
lean_ctor_set(x_26, 0, x_48);
lean_ctor_set_tag(x_21, 4);
lean_ctor_set(x_21, 1, x_46);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set_tag(x_15, 5);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_26);
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
lean_dec(x_6);
switch (lean_obj_tag(x_51)) {
case 0:
{
lean_object* x_52; 
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
case 1:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_Name_str___override(x_53, x_54);
x_56 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_55, x_8, x_9, x_10, x_11, x_47);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_Name_num___override(x_57, x_58);
x_60 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_59, x_8, x_9, x_10, x_11, x_47);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_26);
x_63 = l_Lean_Meta_ppExpr(x_61, x_8, x_9, x_10, x_11, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_23);
x_68 = l_Lean_Meta_getGoalPrefix(x_6);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_tag(x_21, 4);
lean_ctor_set(x_21, 1, x_64);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set_tag(x_15, 5);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_70);
x_71 = lean_ctor_get(x_6, 0);
lean_inc(x_71);
lean_dec(x_6);
switch (lean_obj_tag(x_71)) {
case 0:
{
lean_object* x_72; 
lean_dec(x_7);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_15);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_66);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Name_str___override(x_73, x_74);
x_76 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_75, x_8, x_9, x_10, x_11, x_65);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_66);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_dec(x_71);
x_79 = l_Lean_Name_num___override(x_77, x_78);
x_80 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_79, x_8, x_9, x_10, x_11, x_65);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_81 = lean_ctor_get(x_21, 0);
x_82 = lean_ctor_get(x_21, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_21);
x_83 = lean_ctor_get(x_6, 2);
lean_inc(x_83);
x_84 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_83, x_9, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Meta_ppExpr(x_85, x_8, x_9, x_10, x_11, x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_81);
x_93 = l_Lean_Meta_getGoalPrefix(x_6);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_87)) {
 x_95 = lean_alloc_ctor(5, 2, 0);
} else {
 x_95 = x_87;
 lean_ctor_set_tag(x_95, 5);
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_5);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set_tag(x_15, 5);
lean_ctor_set(x_15, 1, x_96);
lean_ctor_set(x_15, 0, x_95);
x_97 = lean_ctor_get(x_6, 0);
lean_inc(x_97);
lean_dec(x_6);
switch (lean_obj_tag(x_97)) {
case 0:
{
lean_object* x_98; 
lean_dec(x_7);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_15);
lean_ctor_set(x_98, 1, x_90);
return x_98;
}
case 1:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_91);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = l_Lean_Name_str___override(x_99, x_100);
x_102 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_101, x_8, x_9, x_10, x_11, x_90);
return x_102;
}
default: 
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_91);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = l_Lean_Name_num___override(x_103, x_104);
x_106 = l_Lean_Meta_ppGoal___lam__1(x_7, x_15, x_105, x_8, x_9, x_10, x_11, x_90);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_107 = lean_ctor_get(x_15, 0);
x_108 = lean_ctor_get(x_15, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_15);
lean_inc(x_5);
x_109 = l_Lean_Meta_ppGoal_pushPending(x_5, x_17, x_107, x_108, x_8, x_9, x_10, x_11, x_16);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_6, 2);
lean_inc(x_113);
x_114 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_113, x_9, x_111);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = l_Lean_Meta_ppExpr(x_115, x_8, x_9, x_10, x_11, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(x_110);
x_123 = l_Lean_Meta_getGoalPrefix(x_6);
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_117)) {
 x_125 = lean_alloc_ctor(5, 2, 0);
} else {
 x_125 = x_117;
 lean_ctor_set_tag(x_125, 5);
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_112)) {
 x_126 = lean_alloc_ctor(4, 2, 0);
} else {
 x_126 = x_112;
 lean_ctor_set_tag(x_126, 4);
}
lean_ctor_set(x_126, 0, x_5);
lean_ctor_set(x_126, 1, x_119);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_ctor_get(x_6, 0);
lean_inc(x_128);
lean_dec(x_6);
switch (lean_obj_tag(x_128)) {
case 0:
{
lean_object* x_129; 
lean_dec(x_7);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_121;
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_120);
return x_129;
}
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_121);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = l_Lean_Name_str___override(x_130, x_131);
x_133 = l_Lean_Meta_ppGoal___lam__1(x_7, x_127, x_132, x_8, x_9, x_10, x_11, x_120);
return x_133;
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_121);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_dec(x_128);
x_136 = l_Lean_Name_num___override(x_134, x_135);
x_137 = l_Lean_Meta_ppGoal___lam__1(x_7, x_127, x_136, x_8, x_9, x_10, x_11, x_120);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MetavarContext_findDecl_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_mk_string_unchecked("unknown goal", 12, 12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_7);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed), 1, 0);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lean_LocalContext_sanitizeNames(x_19, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_15, 4);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc(x_4);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 12, 7);
lean_closure_set(x_32, 0, x_4);
lean_closure_set(x_32, 1, x_24);
lean_closure_set(x_32, 2, x_30);
lean_closure_set(x_32, 3, x_31);
lean_closure_set(x_32, 4, x_18);
lean_closure_set(x_32, 5, x_15);
lean_closure_set(x_32, 6, x_16);
x_33 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1(lean_box(0), x_24, x_25, x_32, x_2, x_3, x_4, x_5, x_10);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MetavarContext_findDecl_x3f(x_36, x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_mk_string_unchecked("unknown goal", 12, 12);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Lean_Meta_ppGoal_pushPending_spec__0___lam__0___boxed), 1, 0);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 2);
lean_inc(x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_LocalContext_sanitizeNames(x_45, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_41, 4);
lean_inc(x_51);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_unsigned_to_nat(0u);
lean_inc(x_50);
lean_inc(x_4);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___lam__0___boxed), 12, 7);
lean_closure_set(x_58, 0, x_4);
lean_closure_set(x_58, 1, x_50);
lean_closure_set(x_58, 2, x_56);
lean_closure_set(x_58, 3, x_57);
lean_closure_set(x_58, 4, x_44);
lean_closure_set(x_58, 5, x_41);
lean_closure_set(x_58, 6, x_42);
x_59 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1(lean_box(0), x_50, x_51, x_58, x_2, x_3, x_4, x_5, x_35);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LocalContext_foldlM___at___Lean_Meta_ppGoal_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ppGoal___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_ppGoal___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_ppGoal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_auxDecls = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_auxDecls);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_45_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_implementationDetailHyps = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_implementationDetailHyps);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_inaccessibleNames = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_inaccessibleNames);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_PPGoal___hyg_125_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_pp_showLetValues = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_pp_showLetValues);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
