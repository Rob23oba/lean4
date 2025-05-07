// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Lean.Server.Completion.CompletionCollectors Lean.Server.RequestCancellation Std.Data.HashMap
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg___lam__0(lean_object*, lean_object*);
uint64_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2667__spec__0(lean_object*, size_t, size_t, uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1704_(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(size_t, size_t, lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedCompletionItem;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6393_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1169_(uint8_t);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__3(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_string_dec_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_7 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__3(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
x_7 = x_19;
goto block_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_7 = x_24;
goto block_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__2(x_25, x_27);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_7 = x_29;
goto block_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__5(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
x_7 = x_34;
goto block_9;
}
else
{
uint8_t x_35; 
x_35 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__1(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
x_7 = x_35;
goto block_9;
}
}
}
}
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; lean_object* x_82; uint64_t x_83; uint64_t x_84; lean_object* x_97; lean_object* x_98; uint64_t x_99; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_1);
x_10 = lean_string_hash(x_7);
lean_dec(x_7);
x_97 = lean_ctor_get(x_8, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_dec(x_8);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_111; uint64_t x_112; 
x_111 = lean_unsigned_to_nat(11u);
x_112 = lean_uint64_of_nat(x_111);
x_99 = x_112;
goto block_110;
}
else
{
lean_object* x_113; uint64_t x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
x_114 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1704_(x_113);
lean_dec(x_113);
x_115 = lean_unsigned_to_nat(13u);
x_116 = lean_uint64_of_nat(x_115);
x_117 = lean_uint64_mix_hash(x_114, x_116);
x_99 = x_117;
goto block_110;
}
block_39:
{
uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; lean_object* x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_16 = lean_uint64_mix_hash(x_11, x_15);
x_17 = lean_uint64_mix_hash(x_13, x_16);
x_18 = lean_uint64_mix_hash(x_12, x_17);
x_19 = lean_uint64_mix_hash(x_14, x_18);
x_20 = lean_uint64_mix_hash(x_10, x_19);
x_21 = lean_unsigned_to_nat(32u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_unsigned_to_nat(16u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_sub(x_30, x_32);
x_34 = lean_usize_land(x_29, x_33);
x_35 = lean_array_uget(x_1, x_34);
if (lean_is_scalar(x_6)) {
 x_36 = lean_alloc_ctor(1, 3, 0);
} else {
 x_36 = x_6;
}
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_array_uset(x_1, x_34, x_36);
x_1 = x_37;
x_2 = x_5;
goto _start;
}
block_52:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_45; uint64_t x_46; 
x_45 = lean_unsigned_to_nat(11u);
x_46 = lean_uint64_of_nat(x_45);
x_11 = x_44;
x_12 = x_40;
x_13 = x_41;
x_14 = x_43;
x_15 = x_46;
goto block_39;
}
else
{
lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6393_(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(13u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_mix_hash(x_48, x_50);
x_11 = x_44;
x_12 = x_40;
x_13 = x_41;
x_14 = x_43;
x_15 = x_51;
goto block_39;
}
}
block_61:
{
lean_object* x_58; uint64_t x_59; uint64_t x_60; 
x_58 = lean_unsigned_to_nat(13u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_mix_hash(x_57, x_59);
x_40 = x_53;
x_41 = x_54;
x_42 = x_56;
x_43 = x_55;
x_44 = x_60;
goto block_52;
}
block_81:
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_unsigned_to_nat(11u);
x_69 = lean_uint64_of_nat(x_68);
x_40 = x_62;
x_41 = x_65;
x_42 = x_67;
x_43 = x_64;
x_44 = x_69;
goto block_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_unsigned_to_nat(7u);
x_73 = lean_uint64_of_nat(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_71);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_71);
x_53 = x_62;
x_54 = x_65;
x_55 = x_64;
x_56 = x_70;
x_57 = x_73;
goto block_61;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_75, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_dec(x_71);
x_53 = x_62;
x_54 = x_65;
x_55 = x_64;
x_56 = x_70;
x_57 = x_73;
goto block_61;
}
else
{
size_t x_78; size_t x_79; uint64_t x_80; 
x_78 = lean_usize_of_nat(x_74);
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2667__spec__0(x_71, x_78, x_79, x_73);
lean_dec(x_71);
x_53 = x_62;
x_54 = x_65;
x_55 = x_64;
x_56 = x_70;
x_57 = x_80;
goto block_61;
}
}
}
}
block_96:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(11u);
x_88 = lean_uint64_of_nat(x_87);
x_62 = x_84;
x_63 = x_86;
x_64 = x_83;
x_65 = x_88;
goto block_81;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
x_92 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1169_(x_91);
x_93 = lean_unsigned_to_nat(13u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_mix_hash(x_92, x_94);
x_62 = x_84;
x_63 = x_89;
x_64 = x_83;
x_65 = x_95;
goto block_81;
}
}
block_110:
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint64_t x_103; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_unsigned_to_nat(11u);
x_103 = lean_uint64_of_nat(x_102);
x_82 = x_101;
x_83 = x_99;
x_84 = x_103;
goto block_96;
}
else
{
lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_string_hash(x_105);
lean_dec(x_105);
x_107 = lean_unsigned_to_nat(13u);
x_108 = lean_uint64_of_nat(x_107);
x_109 = lean_uint64_mix_hash(x_106, x_108);
x_82 = x_104;
x_83 = x_99;
x_84 = x_109;
goto block_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_53; uint64_t x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; lean_object* x_82; uint64_t x_83; uint64_t x_84; lean_object* x_97; lean_object* x_98; uint64_t x_99; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_1);
x_10 = lean_string_hash(x_7);
lean_dec(x_7);
x_97 = lean_ctor_get(x_8, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_dec(x_8);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_111; uint64_t x_112; 
x_111 = lean_unsigned_to_nat(11u);
x_112 = lean_uint64_of_nat(x_111);
x_99 = x_112;
goto block_110;
}
else
{
lean_object* x_113; uint64_t x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
x_114 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1704_(x_113);
lean_dec(x_113);
x_115 = lean_unsigned_to_nat(13u);
x_116 = lean_uint64_of_nat(x_115);
x_117 = lean_uint64_mix_hash(x_114, x_116);
x_99 = x_117;
goto block_110;
}
block_39:
{
uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; lean_object* x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_uint64_mix_hash(x_11, x_15);
x_17 = lean_uint64_mix_hash(x_12, x_16);
x_18 = lean_uint64_mix_hash(x_13, x_17);
x_19 = lean_uint64_mix_hash(x_14, x_18);
x_20 = lean_uint64_mix_hash(x_10, x_19);
x_21 = lean_unsigned_to_nat(32u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_unsigned_to_nat(16u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_sub(x_30, x_32);
x_34 = lean_usize_land(x_29, x_33);
x_35 = lean_array_uget(x_1, x_34);
if (lean_is_scalar(x_6)) {
 x_36 = lean_alloc_ctor(1, 3, 0);
} else {
 x_36 = x_6;
}
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_array_uset(x_1, x_34, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(x_37, x_5);
return x_38;
}
block_52:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_45; uint64_t x_46; 
x_45 = lean_unsigned_to_nat(11u);
x_46 = lean_uint64_of_nat(x_45);
x_11 = x_44;
x_12 = x_40;
x_13 = x_41;
x_14 = x_43;
x_15 = x_46;
goto block_39;
}
else
{
lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6393_(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(13u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_mix_hash(x_48, x_50);
x_11 = x_44;
x_12 = x_40;
x_13 = x_41;
x_14 = x_43;
x_15 = x_51;
goto block_39;
}
}
block_61:
{
lean_object* x_58; uint64_t x_59; uint64_t x_60; 
x_58 = lean_unsigned_to_nat(13u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_mix_hash(x_57, x_59);
x_40 = x_53;
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
x_44 = x_60;
goto block_52;
}
block_81:
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_unsigned_to_nat(11u);
x_69 = lean_uint64_of_nat(x_68);
x_40 = x_65;
x_41 = x_63;
x_42 = x_67;
x_43 = x_64;
x_44 = x_69;
goto block_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_unsigned_to_nat(7u);
x_73 = lean_uint64_of_nat(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_71);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_71);
x_53 = x_65;
x_54 = x_63;
x_55 = x_70;
x_56 = x_64;
x_57 = x_73;
goto block_61;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_75, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_dec(x_71);
x_53 = x_65;
x_54 = x_63;
x_55 = x_70;
x_56 = x_64;
x_57 = x_73;
goto block_61;
}
else
{
size_t x_78; size_t x_79; uint64_t x_80; 
x_78 = lean_usize_of_nat(x_74);
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2667__spec__0(x_71, x_78, x_79, x_73);
lean_dec(x_71);
x_53 = x_65;
x_54 = x_63;
x_55 = x_70;
x_56 = x_64;
x_57 = x_80;
goto block_61;
}
}
}
}
block_96:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(11u);
x_88 = lean_uint64_of_nat(x_87);
x_62 = x_86;
x_63 = x_84;
x_64 = x_83;
x_65 = x_88;
goto block_81;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
x_92 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1169_(x_91);
x_93 = lean_unsigned_to_nat(13u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_mix_hash(x_92, x_94);
x_62 = x_89;
x_63 = x_84;
x_64 = x_83;
x_65 = x_95;
goto block_81;
}
}
block_110:
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint64_t x_103; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_unsigned_to_nat(11u);
x_103 = lean_uint64_of_nat(x_102);
x_82 = x_101;
x_83 = x_99;
x_84 = x_103;
goto block_96;
}
else
{
lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_string_hash(x_105);
lean_dec(x_105);
x_107 = lean_unsigned_to_nat(13u);
x_108 = lean_uint64_of_nat(x_107);
x_109 = lean_uint64_mix_hash(x_106, x_108);
x_82 = x_104;
x_83 = x_99;
x_84 = x_109;
goto block_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_3 = x_8;
goto block_6;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_3 = x_9;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg___lam__0(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_string_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_12 = x_24;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__3(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_12 = x_29;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
x_12 = x_34;
goto block_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__2(x_35, x_37);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
x_12 = x_39;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__5(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_41);
x_12 = x_44;
goto block_19;
}
else
{
uint8_t x_45; 
x_45 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__1(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_12 = x_45;
goto block_19;
}
}
}
}
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(x_1, x_2, x_10);
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(1, 3, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg___lam__0(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(1, 3, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_10);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_76; uint64_t x_77; uint64_t x_78; lean_object* x_79; uint64_t x_80; uint64_t x_89; uint64_t x_90; uint64_t x_91; lean_object* x_92; uint64_t x_93; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_118; lean_object* x_119; uint64_t x_120; lean_object* x_133; lean_object* x_134; uint64_t x_135; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_22 = x_5;
} else {
 lean_dec_ref(x_5);
 x_22 = lean_box(0);
}
x_23 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_inc(x_23);
x_24 = lean_apply_1(x_1, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_array_get_size(x_21);
x_28 = lean_string_hash(x_25);
lean_dec(x_25);
x_133 = lean_ctor_get(x_26, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_26, 1);
lean_inc(x_134);
lean_dec(x_26);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_147; uint64_t x_148; 
x_147 = lean_unsigned_to_nat(11u);
x_148 = lean_uint64_of_nat(x_147);
x_135 = x_148;
goto block_146;
}
else
{
lean_object* x_149; uint64_t x_150; lean_object* x_151; uint64_t x_152; uint64_t x_153; 
x_149 = lean_ctor_get(x_133, 0);
lean_inc(x_149);
lean_dec(x_133);
x_150 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1704_(x_149);
lean_dec(x_149);
x_151 = lean_unsigned_to_nat(13u);
x_152 = lean_uint64_of_nat(x_151);
x_153 = lean_uint64_mix_hash(x_150, x_152);
x_135 = x_153;
goto block_146;
}
block_75:
{
uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_34 = lean_uint64_mix_hash(x_31, x_33);
x_35 = lean_uint64_mix_hash(x_30, x_34);
x_36 = lean_uint64_mix_hash(x_32, x_35);
x_37 = lean_uint64_mix_hash(x_29, x_36);
x_38 = lean_uint64_mix_hash(x_28, x_37);
x_39 = lean_unsigned_to_nat(32u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_right(x_38, x_40);
x_42 = lean_uint64_xor(x_38, x_41);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_usize_of_nat(x_49);
x_51 = lean_usize_sub(x_48, x_50);
x_52 = lean_usize_land(x_47, x_51);
x_53 = lean_array_uget(x_21, x_52);
lean_inc(x_53);
lean_inc(x_24);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_24, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_mk_empty_array_with_capacity(x_55);
x_57 = lean_array_push(x_56, x_23);
x_58 = lean_nat_add(x_20, x_49);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_53);
x_60 = lean_array_uset(x_21, x_52, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1___redArg(x_60);
if (lean_is_scalar(x_22)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_22;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_6 = x_68;
goto block_11;
}
else
{
lean_object* x_69; 
if (lean_is_scalar(x_22)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_22;
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_6 = x_69;
goto block_11;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_22);
x_70 = lean_box(0);
x_71 = lean_array_uset(x_21, x_52, x_70);
lean_inc(x_24);
x_72 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(x_23, x_24, x_53);
lean_inc(x_72);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_24, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_nat_sub(x_20, x_49);
lean_dec(x_20);
x_12 = x_52;
x_13 = x_71;
x_14 = x_72;
x_15 = x_74;
goto block_18;
}
else
{
x_12 = x_52;
x_13 = x_71;
x_14 = x_72;
x_15 = x_20;
goto block_18;
}
}
}
block_88:
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_81; uint64_t x_82; 
x_81 = lean_unsigned_to_nat(11u);
x_82 = lean_uint64_of_nat(x_81);
x_29 = x_77;
x_30 = x_76;
x_31 = x_80;
x_32 = x_78;
x_33 = x_82;
goto block_75;
}
else
{
lean_object* x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; 
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
x_84 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6393_(x_83);
lean_dec(x_83);
x_85 = lean_unsigned_to_nat(13u);
x_86 = lean_uint64_of_nat(x_85);
x_87 = lean_uint64_mix_hash(x_84, x_86);
x_29 = x_77;
x_30 = x_76;
x_31 = x_80;
x_32 = x_78;
x_33 = x_87;
goto block_75;
}
}
block_97:
{
lean_object* x_94; uint64_t x_95; uint64_t x_96; 
x_94 = lean_unsigned_to_nat(13u);
x_95 = lean_uint64_of_nat(x_94);
x_96 = lean_uint64_mix_hash(x_93, x_95);
x_76 = x_90;
x_77 = x_89;
x_78 = x_91;
x_79 = x_92;
x_80 = x_96;
goto block_88;
}
block_117:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint64_t x_105; 
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_unsigned_to_nat(11u);
x_105 = lean_uint64_of_nat(x_104);
x_76 = x_101;
x_77 = x_99;
x_78 = x_100;
x_79 = x_103;
x_80 = x_105;
goto block_88;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
lean_dec(x_98);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_unsigned_to_nat(7u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_array_get_size(x_107);
x_112 = lean_nat_dec_lt(x_110, x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_107);
x_89 = x_99;
x_90 = x_101;
x_91 = x_100;
x_92 = x_106;
x_93 = x_109;
goto block_97;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_111, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_107);
x_89 = x_99;
x_90 = x_101;
x_91 = x_100;
x_92 = x_106;
x_93 = x_109;
goto block_97;
}
else
{
size_t x_114; size_t x_115; uint64_t x_116; 
x_114 = lean_usize_of_nat(x_110);
x_115 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_116 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2667__spec__0(x_107, x_114, x_115, x_109);
lean_dec(x_107);
x_89 = x_99;
x_90 = x_101;
x_91 = x_100;
x_92 = x_106;
x_93 = x_116;
goto block_97;
}
}
}
}
block_132:
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint64_t x_124; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_unsigned_to_nat(11u);
x_124 = lean_uint64_of_nat(x_123);
x_98 = x_122;
x_99 = x_118;
x_100 = x_120;
x_101 = x_124;
goto block_117;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; 
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
x_128 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1169_(x_127);
x_129 = lean_unsigned_to_nat(13u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_mix_hash(x_128, x_130);
x_98 = x_125;
x_99 = x_118;
x_100 = x_120;
x_101 = x_131;
goto block_117;
}
}
block_146:
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint64_t x_139; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_unsigned_to_nat(11u);
x_139 = lean_uint64_of_nat(x_138);
x_118 = x_135;
x_119 = x_137;
x_120 = x_139;
goto block_132;
}
else
{
lean_object* x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; uint64_t x_144; uint64_t x_145; 
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_string_hash(x_141);
lean_dec(x_141);
x_143 = lean_unsigned_to_nat(13u);
x_144 = lean_uint64_of_nat(x_143);
x_145 = lean_uint64_mix_hash(x_142, x_144);
x_118 = x_135;
x_119 = x_140;
x_120 = x_145;
goto block_132;
}
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_5 = x_6;
goto _start;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uset(x_13, x_12, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_6 = x_17;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_76; uint64_t x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_89; uint64_t x_90; uint64_t x_91; lean_object* x_92; uint64_t x_93; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_118; lean_object* x_119; uint64_t x_120; lean_object* x_133; lean_object* x_134; uint64_t x_135; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_22 = x_5;
} else {
 lean_dec_ref(x_5);
 x_22 = lean_box(0);
}
x_23 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_inc(x_23);
x_24 = lean_apply_1(x_1, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_array_get_size(x_21);
x_28 = lean_string_hash(x_25);
lean_dec(x_25);
x_133 = lean_ctor_get(x_26, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_26, 1);
lean_inc(x_134);
lean_dec(x_26);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_147; uint64_t x_148; 
x_147 = lean_unsigned_to_nat(11u);
x_148 = lean_uint64_of_nat(x_147);
x_135 = x_148;
goto block_146;
}
else
{
lean_object* x_149; uint64_t x_150; lean_object* x_151; uint64_t x_152; uint64_t x_153; 
x_149 = lean_ctor_get(x_133, 0);
lean_inc(x_149);
lean_dec(x_133);
x_150 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1704_(x_149);
lean_dec(x_149);
x_151 = lean_unsigned_to_nat(13u);
x_152 = lean_uint64_of_nat(x_151);
x_153 = lean_uint64_mix_hash(x_150, x_152);
x_135 = x_153;
goto block_146;
}
block_75:
{
uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_34 = lean_uint64_mix_hash(x_31, x_33);
x_35 = lean_uint64_mix_hash(x_29, x_34);
x_36 = lean_uint64_mix_hash(x_32, x_35);
x_37 = lean_uint64_mix_hash(x_30, x_36);
x_38 = lean_uint64_mix_hash(x_28, x_37);
x_39 = lean_unsigned_to_nat(32u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_right(x_38, x_40);
x_42 = lean_uint64_xor(x_38, x_41);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_usize_of_nat(x_49);
x_51 = lean_usize_sub(x_48, x_50);
x_52 = lean_usize_land(x_47, x_51);
x_53 = lean_array_uget(x_21, x_52);
lean_inc(x_53);
lean_inc(x_24);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_24, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_mk_empty_array_with_capacity(x_55);
x_57 = lean_array_push(x_56, x_23);
x_58 = lean_nat_add(x_20, x_49);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_53);
x_60 = lean_array_uset(x_21, x_52, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__1___redArg(x_60);
if (lean_is_scalar(x_22)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_22;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_6 = x_68;
goto block_11;
}
else
{
lean_object* x_69; 
if (lean_is_scalar(x_22)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_22;
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_6 = x_69;
goto block_11;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_22);
x_70 = lean_box(0);
x_71 = lean_array_uset(x_21, x_52, x_70);
lean_inc(x_24);
x_72 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__5___redArg(x_23, x_24, x_53);
lean_inc(x_72);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_24, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_nat_sub(x_20, x_49);
lean_dec(x_20);
x_12 = x_52;
x_13 = x_72;
x_14 = x_71;
x_15 = x_74;
goto block_18;
}
else
{
x_12 = x_52;
x_13 = x_72;
x_14 = x_71;
x_15 = x_20;
goto block_18;
}
}
}
block_88:
{
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_81; uint64_t x_82; 
x_81 = lean_unsigned_to_nat(11u);
x_82 = lean_uint64_of_nat(x_81);
x_29 = x_76;
x_30 = x_77;
x_31 = x_80;
x_32 = x_79;
x_33 = x_82;
goto block_75;
}
else
{
lean_object* x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec(x_78);
x_84 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6393_(x_83);
lean_dec(x_83);
x_85 = lean_unsigned_to_nat(13u);
x_86 = lean_uint64_of_nat(x_85);
x_87 = lean_uint64_mix_hash(x_84, x_86);
x_29 = x_76;
x_30 = x_77;
x_31 = x_80;
x_32 = x_79;
x_33 = x_87;
goto block_75;
}
}
block_97:
{
lean_object* x_94; uint64_t x_95; uint64_t x_96; 
x_94 = lean_unsigned_to_nat(13u);
x_95 = lean_uint64_of_nat(x_94);
x_96 = lean_uint64_mix_hash(x_93, x_95);
x_76 = x_89;
x_77 = x_90;
x_78 = x_92;
x_79 = x_91;
x_80 = x_96;
goto block_88;
}
block_117:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint64_t x_105; 
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_unsigned_to_nat(11u);
x_105 = lean_uint64_of_nat(x_104);
x_76 = x_101;
x_77 = x_99;
x_78 = x_103;
x_79 = x_100;
x_80 = x_105;
goto block_88;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
lean_dec(x_98);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_unsigned_to_nat(7u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_array_get_size(x_107);
x_112 = lean_nat_dec_lt(x_110, x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_107);
x_89 = x_101;
x_90 = x_99;
x_91 = x_100;
x_92 = x_106;
x_93 = x_109;
goto block_97;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_111, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_107);
x_89 = x_101;
x_90 = x_99;
x_91 = x_100;
x_92 = x_106;
x_93 = x_109;
goto block_97;
}
else
{
size_t x_114; size_t x_115; uint64_t x_116; 
x_114 = lean_usize_of_nat(x_110);
x_115 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_116 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2667__spec__0(x_107, x_114, x_115, x_109);
lean_dec(x_107);
x_89 = x_101;
x_90 = x_99;
x_91 = x_100;
x_92 = x_106;
x_93 = x_116;
goto block_97;
}
}
}
}
block_132:
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint64_t x_124; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_unsigned_to_nat(11u);
x_124 = lean_uint64_of_nat(x_123);
x_98 = x_122;
x_99 = x_118;
x_100 = x_120;
x_101 = x_124;
goto block_117;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; 
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
x_128 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1169_(x_127);
x_129 = lean_unsigned_to_nat(13u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_mix_hash(x_128, x_130);
x_98 = x_125;
x_99 = x_118;
x_100 = x_120;
x_101 = x_131;
goto block_117;
}
}
block_146:
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint64_t x_139; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_unsigned_to_nat(11u);
x_139 = lean_uint64_of_nat(x_138);
x_118 = x_135;
x_119 = x_137;
x_120 = x_139;
goto block_132;
}
else
{
lean_object* x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; uint64_t x_144; uint64_t x_145; 
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_string_hash(x_141);
lean_dec(x_141);
x_143 = lean_unsigned_to_nat(13u);
x_144 = lean_uint64_of_nat(x_143);
x_145 = lean_uint64_mix_hash(x_142, x_144);
x_118 = x_135;
x_119 = x_140;
x_120 = x_145;
goto block_132;
}
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg(x_1, x_2, x_3, x_9, x_6);
return x_10;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uset(x_14, x_12, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_6 = x_17;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftl(x_3, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_nextPowerOfTwo(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_size(x_2);
x_14 = lean_usize_of_nat(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg(x_1, x_2, x_13, x_14, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Lsp_instInhabitedCompletionItem;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 1, x_8);
x_1 = x_2;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = l_Lean_Lsp_instInhabitedCompletionItem;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_11, x_14);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_1 = x_16;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__9(x_8, x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 7);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed), 1, 0);
x_3 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(x_6, x_8, x_5);
x_10 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_7, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_11, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
return x_10;
}
else
{
size_t x_14; lean_object* x_15; 
x_14 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_15 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(x_9, x_8, x_14, x_10);
lean_dec(x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6_spec__6(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__6(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_5, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(x_7, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_9 = x_32;
x_10 = x_31;
goto block_13;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_ctor_get(x_27, 2);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_1);
x_37 = l_Lean_Server_Completion_dotCompletion(x_1, x_28, x_36, x_35, x_7, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_9 = x_40;
x_10 = x_39;
goto block_13;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_14 = x_6;
x_15 = x_42;
x_16 = x_41;
goto block_22;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_37;
}
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
x_47 = lean_ctor_get(x_33, 2);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_1);
x_50 = l_Lean_Server_Completion_idCompletion(x_1, x_28, x_48, x_47, x_44, x_45, x_49, x_46, x_7, x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_9 = x_53;
x_10 = x_52;
goto block_13;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_14 = x_6;
x_15 = x_55;
x_16 = x_54;
goto block_22;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_33, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_33, 3);
lean_inc(x_59);
lean_dec(x_33);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_1);
x_61 = l_Lean_Server_Completion_dotIdCompletion(x_1, x_28, x_60, x_58, x_57, x_59, x_7, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_9 = x_64;
x_10 = x_63;
goto block_13;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_14 = x_6;
x_15 = x_66;
x_16 = x_65;
goto block_22;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
}
case 3:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_29, 1);
lean_inc(x_67);
lean_dec(x_29);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_33, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_33, 3);
lean_inc(x_70);
lean_dec(x_33);
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_1);
x_72 = l_Lean_Server_Completion_fieldIdCompletion(x_1, x_28, x_71, x_69, x_68, x_70, x_7, x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_9 = x_75;
x_10 = x_74;
goto block_13;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
lean_dec(x_73);
x_14 = x_6;
x_15 = x_77;
x_16 = x_76;
goto block_22;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_72;
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_29, 1);
lean_inc(x_78);
lean_dec(x_29);
x_79 = lean_ctor_get(x_33, 0);
lean_inc(x_79);
lean_dec(x_33);
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_dec(x_27);
lean_inc(x_2);
lean_inc(x_1);
x_81 = l_Lean_Server_Completion_optionCompletion(x_1, x_28, x_80, x_79, x_2, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_14 = x_6;
x_15 = x_82;
x_16 = x_83;
goto block_22;
}
else
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 7:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_33);
x_88 = lean_ctor_get(x_29, 1);
lean_inc(x_88);
lean_dec(x_29);
x_89 = lean_ctor_get(x_27, 1);
lean_inc(x_89);
lean_dec(x_27);
lean_inc(x_1);
x_90 = l_Lean_Server_Completion_tacticCompletion(x_1, x_28, x_89, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_14 = x_6;
x_15 = x_91;
x_16 = x_92;
goto block_22;
}
else
{
uint8_t x_93; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
default: 
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
x_97 = lean_ctor_get(x_29, 1);
lean_inc(x_97);
lean_dec(x_29);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_98);
x_14 = x_6;
x_15 = x_99;
x_16 = x_97;
goto block_22;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = l_Array_append(lean_box(0), x_14, x_15);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_17;
x_8 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_12, x_13, x_15, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_isEmpty___redArg(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_19;
x_8 = x_18;
goto _start;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_9 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_2, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_size(x_10);
x_15 = lean_usize_of_nat(x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(x_1, x_6, x_10, x_14, x_15, x_13, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_29 = x_16;
} else {
 lean_dec_ref(x_16);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_31 = x_17;
} else {
 lean_dec_ref(x_17);
 x_31 = lean_box(0);
}
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_30);
lean_dec(x_30);
x_38 = lean_unbox(x_11);
lean_dec(x_11);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
x_33 = x_40;
goto block_37;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_33 = x_42;
goto block_37;
}
block_37:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
if (lean_is_scalar(x_29)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_29;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionCollectors(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_RequestCancellation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
